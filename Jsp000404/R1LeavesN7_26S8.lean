import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5518000 in
set_option maxHeartbeats 5518000 in
theorem r1l7_13_24_L_I_M_IR_s0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h3bigk := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
  · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
    · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
        · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
          · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                · linarith only [h0, h13, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h10, h13, h15, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h10, h13, h17, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h10, h12, h17, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h20, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h10, h20, h22, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                    · linarith only [h0, h12, h24, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h10, h12, h26, hlam]
                      · rcases h3bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h0, h10, h20, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h10, h12, h20, h5, h7, hlam, p28_2]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          rcases p28_3 (m.d 0 3) (by simp) with h32 | h32
                          · rcases p28_3 (m.d 1 3) (by simp) with h33 | h33
                            · linarith only [h1, h33, hlam]
                            · linarith only [h10, h33, hlam]
                          · linarith only [h32, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          rcases p28_3 (m.d 0 3) (by simp) with h37 | h37
                          · rcases p28_3 (m.d 1 3) (by simp) with h38 | h38
                            · linarith only [h1, h38, hlam]
                            · linarith only [h11, h38, hlam]
                          · linarith only [h37, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h1, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          rcases p28_3 (m.d 0 3) (by simp) with h44 | h44
                          · rcases p28_3 (m.d 1 3) (by simp) with h45 | h45
                            · rcases p28_3 (m.d 2 3) (by simp) with h46 | h46
                              · linarith only [h46, h8, hlam]
                              · rcases p28_3 (m.d 3 4) (by simp) with h48 | h48
                                · linarith only [h10, h48, hlam]
                                · linarith only [h20, h48, hlam]
                            · linarith only [h45, h8, hlam]
                          · linarith only [h3, h44, hlam]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h1, h20, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h0, h22, h24, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p28_1, u4ehi2]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h3, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h8, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h20, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h22, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h5, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h10, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h10, h12, h5, h7, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h26, hlam, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h6, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h11, hlam, p28_0]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h0, h11, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [h0, h11, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p28_1, u4ehi3]
                        · have p28_0 := h28c.1
                          have p28_1 := h28c.2.1
                          have p28_2 := h28c.2.2.1
                          have p28_3 := h28c.2.2.2
                          linarith only [hlam, p28_0]
            · linarith only [h0, h10, h11, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 4 5 (by decide) (by decide) with h72 | h72
              · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                · linarith only [h0, h10, h3, h71, h73, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h75 | h75
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                    · linarith only [h0, h76, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h2, h72, h76, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h10, h3, h5, h71, h75, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h10, h71, h72, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
              · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                · linarith only [h0, h8, h82, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                  · linarith only [h0, h71, h8, h84, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h86 | h86
                    · linarith only [h0, h86, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h2, h81, h86, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                · linarith only [h0, h10, h3, h5, h7, h8, h81, h89, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h91 | h91
                  · linarith only [h0, h71, h8, h91, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
                    · linarith only [h81, h9, h93, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h95 | h95
                      · linarith only [h0, h3, h5, h81, h95, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · rcases h3bigk with h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h10, h5, h7, h95, hlam, p97_2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h10, h5, h7, h8, h95, hlam, p97_2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 3) (by simp) with h101 | h101
                          · rcases p97_3 (m.d 1 3) (by simp) with h102 | h102
                            · linarith only [h1, h102, hlam]
                            · rcases p97_3 (m.d 2 3) (by simp) with h104 | h104
                              · linarith only [h104, h3, hlam]
                              · rcases p97_3 (m.d 3 4) (by simp) with h106 | h106
                                · linarith only [h106, hlam, p97_0]
                                · rcases p97_3 (m.d 3 5) (by simp) with h108 | h108
                                  · linarith only [h108, h6, hlam]
                                  · linarith only [h108, h95, hlam]
                          · linarith only [h101, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 3) (by simp) with h112 | h112
                          · rcases p97_3 (m.d 1 3) (by simp) with h113 | h113
                            · linarith only [h1, h113, hlam]
                            · rcases p97_3 (m.d 2 3) (by simp) with h115 | h115
                              · linarith only [h115, h3, hlam]
                              · rcases p97_3 (m.d 3 4) (by simp) with h117 | h117
                                · linarith only [h117, h5, hlam]
                                · rcases p97_3 (m.d 3 5) (by simp) with h119 | h119
                                  · linarith only [h119, hlam, p97_0]
                                  · rcases h4bigk with h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c | h121c
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [hlam, p121_0]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      rcases p121_3 (m.d 0 4) (by simp) with h123 | h123
                                      · rcases p121_3 (m.d 1 4) (by simp) with h124 | h124
                                        · linarith only [h124, h2, hlam]
                                        · rcases p121_3 (m.d 2 4) (by simp) with h126 | h126
                                          · linarith only [h126, h4, hlam]
                                          · rcases p121_3 (m.d 3 4) (by simp) with h128 | h128
                                            · linarith only [h128, h5, hlam]
                                            · linarith only [h10, h128, hlam]
                                      · linarith only [h123, h2, hlam]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      rcases p121_3 (m.d 0 4) (by simp) with h132 | h132
                                      · rcases p121_3 (m.d 1 4) (by simp) with h133 | h133
                                        · linarith only [h133, h2, hlam]
                                        · linarith only [h133, h9, hlam]
                                      · linarith only [h132, h4, hlam]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      rcases p121_3 (m.d 0 4) (by simp) with h137 | h137
                                      · rcases p121_3 (m.d 1 4) (by simp) with h138 | h138
                                        · linarith only [h138, h2, hlam]
                                        · rcases p121_3 (m.d 2 4) (by simp) with h140 | h140
                                          · linarith only [h140, h4, hlam]
                                          · rcases p121_3 (m.d 3 4) (by simp) with h142 | h142
                                            · linarith only [h142, h5, hlam]
                                            · rcases p121_3 (m.d 4 5) (by simp) with h144 | h144
                                              · linarith only [h144, h7, hlam]
                                              · linarith only [h144, h95, hlam]
                                      · linarith only [h137, h5, hlam]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h10, h5, h8, h95, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p121_1]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h2, hlam, p121_1]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [hlam, p121_0]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p121_1, u4ehi2]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h10, hlam, p121_1]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h81, hlam, p121_0]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h4, hlam, p121_1]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h9, hlam, p121_1]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [hlam, p121_0]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h89, hlam, p121_1]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h93, hlam, p121_0]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h5, hlam, p121_1]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h95, hc45, hlam, hphi, p121_1, u4ehi1]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h0, h3, h5, h7, h95, hc01, hlam, hphi, ht0b, ht45, ht5b, p121_1, u4ehi2]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [hlam, p121_0]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h95, hlam, p121_0]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h7, hlam, p121_0]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h0, h3, h5, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, p121_1, u4ehi2]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p121_1, u4ehi2]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [h0, h3, h5, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p121_1, u4ehi3]
                                    · have p121_0 := h121c.1
                                      have p121_1 := h121c.2.1
                                      have p121_2 := h121c.2.2.1
                                      have p121_3 := h121c.2.2.2
                                      linarith only [hlam, p121_0]
                          · linarith only [h112, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h1, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h10, hc23, hc34, hlam, hphi, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h10, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h71, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h3, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h8, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h89, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h91, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h5, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, h3, h5, h7, h95, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, h3, h5, h7, h95, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h95, hlam, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h6, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 3) (by simp) with h186 | h186
                          · rcases p97_3 (m.d 1 3) (by simp) with h187 | h187
                            · linarith only [h187, hlam, p97_0]
                            · rcases p97_3 (m.d 2 3) (by simp) with h189 | h189
                              · linarith only [h189, h91, hlam]
                              · rcases p97_3 (m.d 3 4) (by simp) with h191 | h191
                                · linarith only [h191, h95, hlam]
                                · linarith only [h10, h191, hlam]
                          · linarith only [h1, h186, hlam]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 3) (by simp) with h195 | h195
                          · rcases p97_3 (m.d 1 3) (by simp) with h196 | h196
                            · linarith only [h196, h71, hlam]
                            · linarith only [h196, h8, hlam]
                          · linarith only [h195, h3, hlam]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p97_1, u4ehi3]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
          · linarith only [h0, h202, h4, h8, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
            · rcases m.htr 1 4 5 (by decide) (by decide) with h205 | h205
              · rcases m.htr 2 3 4 (by decide) (by decide) with h206 | h206
                · linarith only [h0, h202, h204, h206, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h208 | h208
                  · linarith only [h0, h206, h208, h3, h5, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h204, h206, h208, h3, h5, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h204, h205, h8, h9, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
              · rcases m.htr 2 3 4 (by decide) (by decide) with h213 | h213
                · linarith only [h213, h8, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h215 | h215
                  · linarith only [h0, h204, h213, h215, h3, h5, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h217 | h217
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h218 | h218
                      · rcases h3bigk with h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          rcases p219_3 (m.d 0 3) (by simp) with h221 | h221
                          · rcases p219_3 (m.d 1 3) (by simp) with h222 | h222
                            · linarith only [h1, h222, hlam]
                            · rcases p219_3 (m.d 2 3) (by simp) with h224 | h224
                              · linarith only [h224, h3, hlam]
                              · rcases p219_3 (m.d 3 4) (by simp) with h226 | h226
                                · linarith only [h226, h5, hlam]
                                · linarith only [h202, h226, hlam]
                          · linarith only [h1, h221, hlam]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h213, h5, h8, h9, hlam, p219_2]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h0, h213, h3, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p219_1]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          rcases p219_3 (m.d 0 3) (by simp) with h232 | h232
                          · rcases p219_3 (m.d 1 3) (by simp) with h233 | h233
                            · linarith only [h1, h233, hlam]
                            · rcases p219_3 (m.d 2 3) (by simp) with h235 | h235
                              · linarith only [h235, h3, hlam]
                              · rcases p219_3 (m.d 3 4) (by simp) with h237 | h237
                                · linarith only [h237, h5, hlam]
                                · linarith only [h218, h237, hlam]
                          · linarith only [h232, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h1, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h204, hc23, hc35, hlam, hphi, p219_1]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h202, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h204, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h3, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h8, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h213, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h215, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h5, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          rcases p219_3 (m.d 0 3) (by simp) with h252 | h252
                          · rcases p219_3 (m.d 1 3) (by simp) with h253 | h253
                            · linarith only [h253, hlam, p219_0]
                            · rcases p219_3 (m.d 2 3) (by simp) with h255 | h255
                              · linarith only [h213, h255, hlam]
                              · rcases p219_3 (m.d 3 4) (by simp) with h257 | h257
                                · rcases p219_3 (m.d 3 5) (by simp) with h258 | h258
                                  · linarith only [h218, h258, hlam]
                                  · linarith only [h204, h258, hlam]
                                · linarith only [h257, hlam, p219_0]
                          · linarith only [h1, h252, hlam]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          rcases p219_3 (m.d 0 3) (by simp) with h263 | h263
                          · rcases p219_3 (m.d 1 3) (by simp) with h264 | h264
                            · linarith only [h202, h264, hlam]
                            · linarith only [h264, h8, hlam]
                          · linarith only [h263, h3, hlam]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h0, h204, h3, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p219_1]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h6, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          rcases p219_3 (m.d 0 3) (by simp) with h271 | h271
                          · rcases p219_3 (m.d 1 3) (by simp) with h272 | h272
                            · linarith only [h272, hlam, p219_0]
                            · rcases p219_3 (m.d 2 3) (by simp) with h274 | h274
                              · linarith only [h215, h274, hlam]
                              · rcases p219_3 (m.d 3 4) (by simp) with h276 | h276
                                · rcases p219_3 (m.d 3 5) (by simp) with h277 | h277
                                  · rcases h4bigk with h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c | h278c
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h0, h212, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi4]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h0, h3, h5, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p278_1]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h0, h202, h212, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi4]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      rcases p278_3 (m.d 0 4) (by simp) with h283 | h283
                                      · rcases p278_3 (m.d 1 4) (by simp) with h284 | h284
                                        · linarith only [h2, h284, hlam]
                                        · linarith only [h212, h284, hlam]
                                      · linarith only [h283, hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h2, hlam, p278_1]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h9, hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h202, hlam, p278_1]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi4]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h4, hlam, p278_1]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi1]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h213, hlam, p278_1]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h0, h213, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi4]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h5, hlam, p278_1]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h0, h212, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi4]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi2]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p278_1, u4ehi4]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h7, hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h212, hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h217, hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [h218, hlam, p278_0]
                                    · have p278_0 := h278c.1
                                      have p278_1 := h278c.2.1
                                      have p278_2 := h278c.2.2.1
                                      have p278_3 := h278c.2.2.2
                                      linarith only [hlam, p278_0]
                                  · linarith only [h277, hlam, p219_0]
                                · linarith only [h202, h276, hlam]
                          · linarith only [h1, h271, hlam]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          rcases p219_3 (m.d 0 3) (by simp) with h311 | h311
                          · rcases p219_3 (m.d 1 3) (by simp) with h312 | h312
                            · linarith only [h204, h312, hlam]
                            · linarith only [h312, h8, hlam]
                          · linarith only [h3, h311, hlam]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [h218, hlam, p219_0]
                        · have p219_0 := h219c.1
                          have p219_1 := h219c.2.1
                          have p219_2 := h219c.2.2.1
                          have p219_3 := h219c.2.2.2
                          linarith only [hlam, p219_0]
                      · linarith only [h2, h212, h218, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h212, h217, h9, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                · linarith only [h0, h320, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                  · linarith only [h0, h212, h3, h322, h5, h7, h8, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h324 | h324
                    · linarith only [h212, h320, h324, h8, h9, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h3, h324, h5, h7, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h327 | h327
        · linarith only [h0, h3, h327, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
          · rcases m.htr 1 3 5 (by decide) (by decide) with h330 | h330
            · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
              · rcases m.htr 2 3 4 (by decide) (by decide) with h332 | h332
                · rcases m.htr 2 3 5 (by decide) (by decide) with h333 | h333
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h334 | h334
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h335 | h335
                      · linarith only [h1, h329, h335, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h2, h331, h335, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h327, h331, h334, hlam]
                  · linarith only [h330, h333, h8, hlam]
                · linarith only [h329, h332, h8, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                · rcases m.htr 2 3 5 (by decide) (by decide) with h342 | h342
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h343 | h343
                    · linarith only [h0, h3, h331, h341, h343, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                      · linarith only [h327, h329, h343, h345, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h3bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h0, h3, h329, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi3]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h0, h3, h329, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi3]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          rcases p347_3 (m.d 0 3) (by simp) with h351 | h351
                          · rcases p347_3 (m.d 1 3) (by simp) with h352 | h352
                            · linarith only [h1, h352, hlam]
                            · linarith only [h329, h352, hlam]
                          · linarith only [h351, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          rcases p347_3 (m.d 0 3) (by simp) with h356 | h356
                          · rcases p347_3 (m.d 1 3) (by simp) with h357 | h357
                            · linarith only [h1, h357, hlam]
                            · linarith only [h330, h357, hlam]
                          · linarith only [h356, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h1, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h8, hlam, p347_1]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi3]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h0, h3, h345, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi3]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h3, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h0, h3, h329, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi3]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi3]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h0, h3, h345, hc01, hlam, hphi, ht0b, ht45, ht5b, p347_1, u4ehi3]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h5, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h329, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h341, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h345, hlam, p347_1]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h6, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h330, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h342, hlam, p347_0]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [h330, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p347_1, u4ehi3]
                        · have p347_0 := h347c.1
                          have p347_1 := h347c.2.1
                          have p347_2 := h347c.2.2.1
                          have p347_3 := h347c.2.2.2
                          linarith only [hlam, p347_0]
                  · linarith only [h330, h342, h8, hlam]
                · linarith only [h329, h341, h8, hlam]
            · linarith only [h0, h3, h329, h330, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h384 | h384
            · rcases m.htr 1 4 5 (by decide) (by decide) with h385 | h385
              · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                · linarith only [h0, h3, h329, h384, h386, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h389 | h389
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h390 | h390
                      · linarith only [h0, h3, h384, h386, h390, h5, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h327, h384, h385, h386, h390, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h327, h384, h385, h386, h389, h5, h8, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                  · linarith only [h384, h388, h8, hlam]
              · linarith only [h329, h384, h385, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h396 | h396
              · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
                · linarith only [h0, h3, h329, h396, h397, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h399 | h399
                  · linarith only [h384, h397, h399, h8, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h401 | h401
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h402 | h402
                      · rcases h3bigk with h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          rcases p403_3 (m.d 0 3) (by simp) with h405 | h405
                          · rcases p403_3 (m.d 1 3) (by simp) with h406 | h406
                            · linarith only [h1, h406, hlam]
                            · rcases p403_3 (m.d 2 3) (by simp) with h408 | h408
                              · linarith only [h3, h408, hlam]
                              · linarith only [h408, h8, hlam]
                          · linarith only [h1, h405, hlam]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          rcases p403_3 (m.d 0 3) (by simp) with h412 | h412
                          · rcases p403_3 (m.d 1 3) (by simp) with h413 | h413
                            · linarith only [h1, h413, hlam]
                            · rcases p403_3 (m.d 2 3) (by simp) with h415 | h415
                              · linarith only [h3, h415, hlam]
                              · rcases p403_3 (m.d 3 4) (by simp) with h417 | h417
                                · linarith only [h417, h5, hlam]
                                · linarith only [h397, h417, hlam]
                          · linarith only [h3, h412, hlam]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h0, h3, h399, h402, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h0, h3, h399, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h1, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h8, hlam, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h329, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h384, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h3, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h399, h402, hc13, hc34, hlam, hphi, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h397, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h399, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h5, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          rcases p403_3 (m.d 0 3) (by simp) with h434 | h434
                          · rcases p403_3 (m.d 1 3) (by simp) with h435 | h435
                            · linarith only [h435, hlam, p403_0]
                            · rcases p403_3 (m.d 2 3) (by simp) with h437 | h437
                              · linarith only [h397, h437, hlam]
                              · linarith only [h437, h8, hlam]
                          · linarith only [h1, h434, hlam]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h0, h3, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h0, h3, h384, h5, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h6, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          rcases p403_3 (m.d 0 3) (by simp) with h445 | h445
                          · rcases p403_3 (m.d 1 3) (by simp) with h446 | h446
                            · linarith only [h446, hlam, p403_0]
                            · rcases p403_3 (m.d 2 3) (by simp) with h448 | h448
                              · linarith only [h399, h448, hlam]
                              · linarith only [h448, h8, hlam]
                          · linarith only [h1, h445, hlam]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h8, hc12, hc35, hlam, hphi, ht23, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h402, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                      · linarith only [h2, h396, h402, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h327, h396, h401, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h457 | h457
                · rcases m.htr 2 3 5 (by decide) (by decide) with h458 | h458
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
                    · linarith only [h0, h3, h396, h457, h459, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h461 | h461
                      · linarith only [h457, h459, h461, hlam]
                      · rcases h3bigk with h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c | h463c
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h329, h457, h459, h5, h7, hlam, p463_2]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h0, h3, h384, h458, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p463_1]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          rcases p463_3 (m.d 0 3) (by simp) with h467 | h467
                          · rcases p463_3 (m.d 1 3) (by simp) with h468 | h468
                            · linarith only [h1, h468, hlam]
                            · rcases p463_3 (m.d 2 3) (by simp) with h470 | h470
                              · linarith only [h3, h470, hlam]
                              · linarith only [h457, h470, hlam]
                          · linarith only [h467, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          rcases p463_3 (m.d 0 3) (by simp) with h474 | h474
                          · rcases p463_3 (m.d 1 3) (by simp) with h475 | h475
                            · linarith only [h1, h475, hlam]
                            · rcases p463_3 (m.d 2 3) (by simp) with h477 | h477
                              · linarith only [h3, h477, hlam]
                              · linarith only [h458, h477, hlam]
                          · linarith only [h474, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h1, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h8, hlam, p463_1]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h329, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h384, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h3, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          rcases p463_3 (m.d 0 3) (by simp) with h487 | h487
                          · rcases p463_3 (m.d 1 3) (by simp) with h488 | h488
                            · linarith only [h488, h8, hlam]
                            · rcases p463_3 (m.d 2 3) (by simp) with h490 | h490
                              · rcases p463_3 (m.d 3 4) (by simp) with h491 | h491
                                · linarith only [h457, h491, hlam]
                                · linarith only [h329, h491, hlam]
                              · linarith only [h490, h8, hlam]
                          · linarith only [h1, h487, hlam]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p463_1, u4ehi3]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h0, h3, h329, h461, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p463_1]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h5, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h0, h3, h457, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p463_1]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h457, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h461, hlam, p463_1]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h6, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h0, h3, h458, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p463_1]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h458, hlam, p463_0]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [h0, h3, h458, hc01, hlam, hphi, ht0b, ht45, ht5b, p463_1, u4ehi3]
                        · have p463_0 := h463c.1
                          have p463_1 := h463c.2.1
                          have p463_2 := h463c.2.2.1
                          have p463_3 := h463c.2.2.2
                          linarith only [hlam, p463_0]
                  · linarith only [h0, h3, h329, h457, h458, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h510 | h510
                  · linarith only [h384, h457, h510, h8, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h512 | h512
                    · linarith only [h0, h396, h4, h512, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h514 | h514
                      · linarith only [h0, h3, h457, h5, h512, h514, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h457, h514, h8, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h517 | h517
      · rcases m.htr 1 2 4 (by decide) (by decide) with h518 | h518
        · rcases m.htr 1 3 4 (by decide) (by decide) with h519 | h519
          · rcases m.htr 1 3 5 (by decide) (by decide) with h520 | h520
            · rcases m.htr 1 4 5 (by decide) (by decide) with h521 | h521
              · linarith only [h2, h521, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h523 | h523
                · linarith only [h0, h517, h523, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h525 | h525
                  · linarith only [h1, h519, h523, h525, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h527 | h527
                    · linarith only [h0, h2, h4, h519, h523, h527, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h529 | h529
                      · linarith only [h2, h519, h529, h7, hlam]
                      · rcases h3bigk with h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c | h531c
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h0, h3, h520, h525, h527, hc01, hlam, hphi, ht0b, ht45, ht5b, p531_1, u4ehi2]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          rcases p531_3 (m.d 0 3) (by simp) with h534 | h534
                          · rcases p531_3 (m.d 1 3) (by simp) with h535 | h535
                            · linarith only [h1, h535, hlam]
                            · linarith only [h517, h535, hlam]
                          · linarith only [h3, h534, hlam]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          rcases p531_3 (m.d 0 3) (by simp) with h539 | h539
                          · rcases p531_3 (m.d 1 3) (by simp) with h540 | h540
                            · linarith only [h1, h540, hlam]
                            · linarith only [h519, h540, hlam]
                          · linarith only [h539, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          rcases p531_3 (m.d 0 3) (by simp) with h544 | h544
                          · rcases p531_3 (m.d 1 3) (by simp) with h545 | h545
                            · linarith only [h1, h545, hlam]
                            · linarith only [h520, h545, hlam]
                          · linarith only [h544, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h1, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          rcases p531_3 (m.d 0 3) (by simp) with h551 | h551
                          · rcases p531_3 (m.d 1 3) (by simp) with h552 | h552
                            · rcases p531_3 (m.d 2 3) (by simp) with h553 | h553
                              · linarith only [h517, h553, hlam]
                              · rcases p531_3 (m.d 3 4) (by simp) with h555 | h555
                                · linarith only [h519, h555, hlam]
                                · linarith only [h523, h555, hlam]
                            · linarith only [h517, h552, hlam]
                          · linarith only [h3, h551, hlam]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h0, h517, h523, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p531_1]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h0, h517, h525, h527, hc01, hlam, hphi, ht0b, ht45, ht5b, p531_1, u4ehi2]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h3, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h517, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h523, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h525, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h5, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h519, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h2, h519, h7, hc23, hc45, hlam, hphi, ht34, p531_1]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h529, hlam, p531_1]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h6, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h520, hlam, p531_0]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h0, h517, h520, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p531_1]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [h0, h517, h520, hc01, hlam, hphi, ht0b, ht45, ht5b, p531_1, u4ehi3]
                        · have p531_0 := h531c.1
                          have p531_1 := h531c.2.1
                          have p531_2 := h531c.2.2.1
                          have p531_3 := h531c.2.2.2
                          linarith only [hlam, p531_0]
            · linarith only [h0, h3, h519, h520, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h578 | h578
            · rcases m.htr 1 4 5 (by decide) (by decide) with h579 | h579
              · linarith only [h5, h519, h579, h7, hlam]
              · linarith only [h5, h519, h578, h579, h7, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h582 | h582
              · linarith only [h2, h582, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h584 | h584
                · linarith only [h517, h519, h584, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h586 | h586
                  · linarith only [h5, h517, h519, h578, h582, h586, h7, hc45, hlam, hphi, u4ehi1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h588 | h588
                    · linarith only [h2, h518, h588, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h590 | h590
                      · linarith only [h5, h590, h7, hlam]
                      · rcases h3bigk with h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          rcases p592_3 (m.d 0 3) (by simp) with h594 | h594
                          · rcases p592_3 (m.d 1 3) (by simp) with h595 | h595
                            · linarith only [h1, h595, hlam]
                            · rcases p592_3 (m.d 2 3) (by simp) with h597 | h597
                              · linarith only [h3, h597, hlam]
                              · rcases p592_3 (m.d 3 4) (by simp) with h599 | h599
                                · linarith only [h5, h599, hlam]
                                · linarith only [h519, h599, hlam]
                          · linarith only [h1, h594, hlam]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          rcases p592_3 (m.d 0 3) (by simp) with h603 | h603
                          · rcases p592_3 (m.d 1 3) (by simp) with h604 | h604
                            · linarith only [h1, h604, hlam]
                            · linarith only [h517, h604, hlam]
                          · linarith only [h3, h603, hlam]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          rcases p592_3 (m.d 0 3) (by simp) with h608 | h608
                          · rcases p592_3 (m.d 1 3) (by simp) with h609 | h609
                            · linarith only [h1, h609, hlam]
                            · rcases p592_3 (m.d 2 3) (by simp) with h611 | h611
                              · linarith only [h3, h611, hlam]
                              · rcases p592_3 (m.d 3 4) (by simp) with h613 | h613
                                · linarith only [h613, hlam, p592_0]
                                · rcases p592_3 (m.d 3 5) (by simp) with h615 | h615
                                  · linarith only [h6, h615, hlam]
                                  · linarith only [h590, h615, hlam]
                          · linarith only [h608, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          rcases p592_3 (m.d 0 3) (by simp) with h619 | h619
                          · rcases p592_3 (m.d 1 3) (by simp) with h620 | h620
                            · linarith only [h1, h620, hlam]
                            · rcases p592_3 (m.d 2 3) (by simp) with h622 | h622
                              · linarith only [h3, h622, hlam]
                              · rcases p592_3 (m.d 3 4) (by simp) with h624 | h624
                                · linarith only [h5, h624, hlam]
                                · rcases p592_3 (m.d 3 5) (by simp) with h626 | h626
                                  · linarith only [h626, hlam, p592_0]
                                  · rcases h4bigk with h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c | h628c
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h7, hc45, hlam, hphi, p628_1, u4ehi1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h7, hc45, hlam, hphi, p628_1, u4ehi2]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h7, hc45, hlam, hphi, p628_1, u4ehi3]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h7, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h2, hlam, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p628_1, u4ehi2]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h519, hlam, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h582, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h4, hlam, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h518, hlam, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h584, hlam, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h588, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h5, hlam, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h0, h3, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p628_1, u4ehi1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h5, h7, hc45, hlam, hphi, p628_1, u4ehi2]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h590, hlam, p628_0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hc45, hlam, hphi, p628_1, u4ehi0]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h518, hc45, hlam, hphi, p628_1, u4ehi2]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hc45, hlam, hphi, p628_1, u4ehi2]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [h517, h519, hc23, hc45, hlam, hphi, ht34, p628_1]
                                    · have p628_0 := h628c.1
                                      have p628_1 := h628c.2.1
                                      have p628_2 := h628c.2.2.1
                                      have p628_3 := h628c.2.2.2
                                      linarith only [hlam, p628_0]
                          · linarith only [h619, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h1, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h519, hc23, hc34, hlam, hphi, p592_1]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h519, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h578, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h3, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h517, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h584, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h586, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h5, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h5, h7, hc13, hc45, hlam, hphi, ht34, p592_1]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h5, h7, hc23, hc45, hlam, hphi, ht34, p592_1]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h590, hlam, p592_1]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h6, hlam, p592_0]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          rcases p592_3 (m.d 0 3) (by simp) with h671 | h671
                          · rcases p592_3 (m.d 1 3) (by simp) with h672 | h672
                            · linarith only [h672, hlam, p592_0]
                            · rcases p592_3 (m.d 2 3) (by simp) with h674 | h674
                              · linarith only [h586, h674, hlam]
                              · rcases p592_3 (m.d 3 4) (by simp) with h676 | h676
                                · linarith only [h590, h676, hlam]
                                · linarith only [h519, h676, hlam]
                          · linarith only [h1, h671, hlam]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          rcases p592_3 (m.d 0 3) (by simp) with h680 | h680
                          · rcases p592_3 (m.d 1 3) (by simp) with h681 | h681
                            · linarith only [h578, h681, hlam]
                            · linarith only [h517, h681, hlam]
                          · linarith only [h3, h680, hlam]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p592_1, u4ehi3]
                        · have p592_0 := h592c.1
                          have p592_1 := h592c.2.1
                          have p592_2 := h592c.2.2.1
                          have p592_3 := h592c.2.2.2
                          linarith only [hlam, p592_0]
        · linarith only [h4, h517, h518, h7, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h688 | h688
        · linarith only [h0, h3, h517, h688, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h690 | h690
          · rcases m.htr 1 3 5 (by decide) (by decide) with h691 | h691
            · rcases m.htr 1 4 5 (by decide) (by decide) with h692 | h692
              · linarith only [h2, h4, h688, h692, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h694 | h694
                · rcases m.htr 2 3 5 (by decide) (by decide) with h695 | h695
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h696 | h696
                    · linarith only [h4, h696, h7, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h698 | h698
                      · linarith only [h4, h688, h690, h698, h7, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · rcases h3bigk with h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c | h700c
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h0, h3, h690, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi3]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h0, h3, h517, h690, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi3]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          rcases p700_3 (m.d 0 3) (by simp) with h704 | h704
                          · rcases p700_3 (m.d 1 3) (by simp) with h705 | h705
                            · linarith only [h1, h705, hlam]
                            · linarith only [h690, h705, hlam]
                          · linarith only [h704, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          rcases p700_3 (m.d 0 3) (by simp) with h709 | h709
                          · rcases p700_3 (m.d 1 3) (by simp) with h710 | h710
                            · linarith only [h1, h710, hlam]
                            · linarith only [h691, h710, hlam]
                          · linarith only [h709, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h1, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h517, hlam, p700_1]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi3]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h0, h3, h517, h698, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi3]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h3, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h0, h3, h690, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi3]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi3]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h0, h3, h698, hc01, hlam, hphi, ht0b, ht45, ht5b, p700_1, u4ehi3]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h5, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h690, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h694, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h698, hlam, p700_1]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h6, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h691, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h695, hlam, p700_0]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [h691, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p700_1, u4ehi3]
                        · have p700_0 := h700c.1
                          have p700_1 := h700c.2.1
                          have p700_2 := h700c.2.2.1
                          have p700_3 := h700c.2.2.2
                          linarith only [hlam, p700_0]
                  · linarith only [h517, h691, h695, hlam]
                · linarith only [h5, h517, h694, h7, hc12, hc45, hlam, hphi, ht23, ht34]
            · linarith only [h6, h690, h691, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h737 | h737
            · rcases m.htr 1 4 5 (by decide) (by decide) with h738 | h738
              · linarith only [h5, h690, h7, h737, h738, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h5, h690, h7, h737, h738, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h741 | h741
              · linarith only [h2, h7, h741, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h743 | h743
                · rcases m.htr 2 3 5 (by decide) (by decide) with h744 | h744
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h745 | h745
                    · linarith only [h4, h7, h745, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h747 | h747
                      · linarith only [h4, h7, h743, h747, hlam]
                      · rcases h3bigk with h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c | h749c
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 3) (by simp) with h751 | h751
                          · rcases p749_3 (m.d 1 3) (by simp) with h752 | h752
                            · linarith only [h1, h752, hlam]
                            · rcases p749_3 (m.d 2 3) (by simp) with h754 | h754
                              · linarith only [h3, h754, hlam]
                              · linarith only [h517, h754, hlam]
                          · linarith only [h1, h751, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h0, h3, h517, h690, h743, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 3) (by simp) with h759 | h759
                          · rcases p749_3 (m.d 1 3) (by simp) with h760 | h760
                            · linarith only [h1, h760, hlam]
                            · rcases p749_3 (m.d 2 3) (by simp) with h762 | h762
                              · linarith only [h3, h762, hlam]
                              · linarith only [h743, h762, hlam]
                          · linarith only [h759, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 3) (by simp) with h766 | h766
                          · rcases p749_3 (m.d 1 3) (by simp) with h767 | h767
                            · linarith only [h1, h767, hlam]
                            · rcases p749_3 (m.d 2 3) (by simp) with h769 | h769
                              · linarith only [h3, h769, hlam]
                              · linarith only [h744, h769, hlam]
                          · linarith only [h766, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h1, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h517, hlam, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h690, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h737, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h3, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          rcases p749_3 (m.d 0 3) (by simp) with h779 | h779
                          · rcases p749_3 (m.d 1 3) (by simp) with h780 | h780
                            · linarith only [h517, h780, hlam]
                            · rcases p749_3 (m.d 2 3) (by simp) with h782 | h782
                              · rcases p749_3 (m.d 3 4) (by simp) with h783 | h783
                                · linarith only [h743, h783, hlam]
                                · linarith only [h690, h783, hlam]
                              · linarith only [h517, h782, hlam]
                          · linarith only [h1, h779, hlam]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h517, h690, hc12, hc23, hlam, hphi, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h0, h3, h517, h690, h747, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h5, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h4, h517, h7, h743, hc12, hc45, hlam, hphi, ht23, ht34, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h743, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h747, hlam, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h6, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h0, h3, h517, h744, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p749_1]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h744, hlam, p749_0]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [h0, h3, h744, hc01, hlam, hphi, ht0b, ht45, ht5b, p749_1, u4ehi3]
                        · have p749_0 := h749c.1
                          have p749_1 := h749c.2.1
                          have p749_2 := h749c.2.2.1
                          have p749_3 := h749c.2.2.2
                          linarith only [hlam, p749_0]
                  · linarith only [h0, h3, h517, h6, h690, h743, h744, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h5, h517, h7, h743, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h803 | h803
    · linarith only [h5, h6, h803, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h805 | h805
      · rcases m.htr 1 2 4 (by decide) (by decide) with h806 | h806
        · rcases m.htr 1 3 4 (by decide) (by decide) with h807 | h807
          · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
            · linarith only [h1, h6, h808, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h810 | h810
              · linarith only [h2, h803, h810, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h812 | h812
                · linarith only [h0, h805, h812, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                · linarith only [h1, h6, h807, h812, hc23, hc35, hlam, hphi]
          · linarith only [h5, h6, h807, hc13, hc35, hlam, hphi]
        · linarith only [h4, h803, h805, h806, hc23, hc45, hlam, hphi, ht34]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h817 | h817
        · linarith only [h0, h3, h805, h817, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h819 | h819
          · rcases m.htr 1 3 5 (by decide) (by decide) with h820 | h820
            · linarith only [h3, h6, h805, h820, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h822 | h822
              · linarith only [h4, h803, h817, h822, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h824 | h824
                · rcases m.htr 2 3 5 (by decide) (by decide) with h825 | h825
                  · linarith only [h3, h6, h825, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h827 | h827
                    · linarith only [h4, h803, h827, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h829 | h829
                      · linarith only [h3, h6, h803, h805, h819, h829, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                      · linarith only [h3, h6, h805, h819, h829, hc45, hlam, hphi, u4ehi3]
                · linarith only [h805, h819, h824, hlam]
          · linarith only [h5, h6, h819, hc13, hc35, hlam, hphi]

end R2N4
