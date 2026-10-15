import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3690000 in
set_option maxHeartbeats 3690000 in
theorem r1l7_13_24_L_R_M_IR_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
    · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
      · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
            · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h11, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h14, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h14, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                    · linarith only [h18, h7, h9, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h0, h20, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h17, h2, h20, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                    · linarith only [h0, h17, h23, h3, h6, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                      · linarith only [h0, h17, h25, h3, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                        · linarith only [h17, h27, h7, h9, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h27, h7, h9, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h3, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
              · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                      · linarith only [h31, h35, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h2, h33, h35, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h31, h33, h34, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h39 | h39
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
                      · linarith only [h31, h33, h40, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h42 | h42
                        · linarith only [h31, h33, h39, h42, hlam]
                        · rcases h4bigk with h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            rcases p44_3 (m.d 0 4) (by simp) with h46 | h46
                            · rcases p44_3 (m.d 1 4) (by simp) with h47 | h47
                              · linarith only [h2, h47, hlam]
                              · rcases p44_3 (m.d 2 4) (by simp) with h49 | h49
                                · linarith only [h3, h49, hlam]
                                · rcases p44_3 (m.d 3 4) (by simp) with h51 | h51
                                  · linarith only [h4, h51, hlam]
                                  · rcases p44_3 (m.d 4 5) (by simp) with h53 | h53
                                    · linarith only [h53, h6, hlam]
                                    · linarith only [h33, h53, hlam]
                            · linarith only [h2, h46, hlam]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            rcases p44_3 (m.d 0 4) (by simp) with h57 | h57
                            · rcases p44_3 (m.d 1 4) (by simp) with h58 | h58
                              · linarith only [h2, h58, hlam]
                              · linarith only [h31, h58, hlam]
                            · linarith only [h3, h57, hlam]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            rcases p44_3 (m.d 0 4) (by simp) with h62 | h62
                            · rcases p44_3 (m.d 1 4) (by simp) with h63 | h63
                              · linarith only [h2, h63, hlam]
                              · linarith only [h32, h63, hlam]
                            · linarith only [h4, h62, hlam]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h3, h31, h33, h39, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1, u3ehi3]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h2, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h33, h39, hc45, hlam, hphi, ht34, p44_1, u3ehi3]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h3, h33, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1, u3ehi3]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h33, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h3, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h31, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1, u3ehi3]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h40, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h4, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h32, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h39, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h42, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h6, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p44_1, u4ehi1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h3, h39, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1, u3ehi3]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1, u3ehi3]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                    · linarith only [h1, h31, h39, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h1, h31, h32, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                · rcases m.htr 1 4 5 (by decide) (by decide) with h91 | h91
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h93 | h93
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h94 | h94
                        · linarith only [h1, h90, h94, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h2, h91, h94, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h31, h91, h93, hlam]
                    · linarith only [h7, h90, h92, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h100 | h100
                      · linarith only [h0, h100, h3, h91, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                        · linarith only [h100, h102, h90, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · rcases h4bigk with h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            rcases p104_3 (m.d 0 4) (by simp) with h106 | h106
                            · rcases p104_3 (m.d 1 4) (by simp) with h107 | h107
                              · linarith only [h107, h2, hlam]
                              · rcases p104_3 (m.d 2 4) (by simp) with h109 | h109
                                · linarith only [h109, h3, hlam]
                                · linarith only [h109, h31, hlam]
                            · linarith only [h106, h2, hlam]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            rcases p104_3 (m.d 0 4) (by simp) with h113 | h113
                            · rcases p104_3 (m.d 1 4) (by simp) with h114 | h114
                              · linarith only [h114, h2, hlam]
                              · rcases p104_3 (m.d 2 4) (by simp) with h116 | h116
                                · linarith only [h116, h3, hlam]
                                · rcases p104_3 (m.d 3 4) (by simp) with h118 | h118
                                  · linarith only [h118, h4, hlam]
                                  · rcases p104_3 (m.d 4 5) (by simp) with h120 | h120
                                    · linarith only [h120, h6, hlam]
                                    · linarith only [h100, h120, hlam]
                            · linarith only [h113, h3, hlam]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            rcases p104_3 (m.d 0 4) (by simp) with h124 | h124
                            · rcases p104_3 (m.d 1 4) (by simp) with h125 | h125
                              · linarith only [h125, h2, hlam]
                              · linarith only [h125, h90, hlam]
                            · linarith only [h124, h4, hlam]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h0, h100, h3, h31, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p104_1, u3ehi3]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h2, hlam, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h31, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h100, h31, hc45, hlam, hphi, ht34, p104_1, u3ehi3]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h91, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h3, hlam, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h100, hc45, hlam, hphi, p104_1, u4ehi1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h0, h100, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p104_1, u3ehi3]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h100, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h4, hlam, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h90, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h99, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h102, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h6, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p104_1, u4ehi1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h0, h3, h31, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p104_1, u3ehi3]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                    · linarith only [h7, h90, h99, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h153 | h153
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h154 | h154
                        · rcases h4bigk with h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c | h155c
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h0, h151, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p155_1, u4ehi4]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h0, h152, h3, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p155_1, u3ehi1]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h0, h3, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p155_1, u3ehi1]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            rcases p155_3 (m.d 0 4) (by simp) with h160 | h160
                            · rcases p155_3 (m.d 1 4) (by simp) with h161 | h161
                              · linarith only [h161, h2, hlam]
                              · linarith only [h151, h161, hlam]
                            · linarith only [h160, hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h2, hlam, p155_1]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h31, hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h90, hlam, p155_1]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p155_1, u4ehi4]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h3, hlam, p155_1]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p155_1, u4ehi1]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h0, h3, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p155_1, u3ehi1]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p155_1, u4ehi4]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h4, hlam, p155_1]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h151, h152, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p155_1, u4ehi4]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h152, hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h152, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p155_1, u4ehi4]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h6, hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h151, hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h153, hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [h154, hlam, p155_0]
                          · have p155_0 := h155c.1
                            have p155_1 := h155c.2.1
                            have p155_2 := h155c.2.2.1
                            have p155_3 := h155c.2.2.2
                            linarith only [hlam, p155_0]
                        · linarith only [h151, h154, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h151, h152, h153, h90, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
                        · rcases h4bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h0, h151, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p189_1, u4ehi4]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h0, h151, h3, h31, hc01, hlam, hphi, ht0b, ht45, ht5b, p189_1, u4ehi4]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h0, h152, h3, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            rcases p189_3 (m.d 0 4) (by simp) with h194 | h194
                            · rcases p189_3 (m.d 1 4) (by simp) with h195 | h195
                              · linarith only [h195, h2, hlam]
                              · linarith only [h151, h195, hlam]
                            · linarith only [h194, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h2, hlam, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h31, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h90, hlam, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p189_1, u4ehi4]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h3, hlam, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p189_1, u4ehi1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h152, hlam, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p189_1, u4ehi4]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h4, hlam, p189_1]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h1, h151, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p189_1, u4ehi4]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p189_1, u4ehi2]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p189_1, u4ehi4]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h6, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h151, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h187, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [h188, hlam, p189_0]
                          · have p189_0 := h189c.1
                            have p189_1 := h189c.2.1
                            have p189_2 := h189c.2.2.1
                            have p189_3 := h189c.2.2.2
                            linarith only [hlam, p189_0]
                        · linarith only [h151, h188, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h151, h187, h31, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h222 | h222
                      · linarith only [h0, h151, h222, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h0, h221, h222, h3, h6, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h225 | h225
                      · linarith only [h0, h151, h225, h3, h90, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h227 | h227
                        · linarith only [h1, h225, h227, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h227, h90, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
            · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
              · rcases m.htr 1 3 4 (by decide) (by decide) with h232 | h232
                · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
                  · linarith only [h2, h233, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                    · linarith only [h0, h230, h235, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h2, h232, h235, h6, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h232, h4, h6, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h230, h231, h3, h6, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
              · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
                · rcases m.htr 1 4 5 (by decide) (by decide) with h242 | h242
                  · linarith only [h2, h242, h6, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h245 | h245
                      · linarith only [h240, h245, h6, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                        · linarith only [h2, h240, h244, h247, h6, hlam]
                        · rcases h4bigk with h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c | h249c
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h240, h244, h6, hc45, hlam, hphi, ht34, p249_1, u3ehi3]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h244, h6, hc45, hlam, hphi, ht34, p249_1, u3ehi3]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h6, hc45, hlam, hphi, ht34, p249_1, u3ehi3]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h6, hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h2, hlam, p249_1]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h2, h244, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1, u3ehi3]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h2, h6, hc45, hlam, hphi, ht34, p249_1, u3ehi3]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h242, hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h3, hlam, p249_1]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h240, hlam, p249_1]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p249_1, u3ehi3]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h245, hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h4, hlam, p249_1]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h241, hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h244, hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h247, hlam, p249_0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [hc45, hlam, hphi, p249_1, u4ehi0]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h241, hc45, hlam, hphi, ht34, p249_1, u3ehi3]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [h244, hc45, hlam, hphi, ht34, p249_1, u3ehi3]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p249_1, u3ehi3]
                          · have p249_0 := h249c.1
                            have p249_1 := h249c.2.1
                            have p249_2 := h249c.2.2.1
                            have p249_3 := h249c.2.2.2
                            linarith only [hlam, p249_0]
                    · linarith only [h230, h244, h4, h6, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h241, h4, h6, hc45, hlam, hphi, ht34, u3ehi1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                  · linarith only [h2, h278, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h281 | h281
                      · linarith only [h281, h3, h6, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h283 | h283
                        · linarith only [h1, h277, h283, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                        · rcases h4bigk with h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c | h285c
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h277, h6, hc45, hlam, hphi, ht34, p285_1, u3ehi3]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h240, h277, h6, hc45, hlam, hphi, ht34, p285_1, u3ehi3]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h6, hc45, hlam, hphi, ht34, p285_1, u3ehi3]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h6, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h2, hlam, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h240, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1, u3ehi3]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h278, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h3, hlam, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p285_1, u4ehi1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h3, h6, hc45, hlam, hphi, ht34, p285_1, u3ehi3]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h281, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h4, hlam, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h277, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h280, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h283, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hc45, hlam, hphi, p285_1, u4ehi0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h277, hc45, hlam, hphi, ht34, p285_1, u3ehi3]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h240, hc12, hc45, hlam, hphi, ht23, ht34, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p285_1, u3ehi3]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                    · linarith only [h240, h277, h280, h3, h6, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h277, h4, h6, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h4, h5, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h314 | h314
        · linarith only [h314, h4, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
          · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
            · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
              · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                · linarith only [h1, h319, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                    · linarith only [h0, h317, h322, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h324 | h324
                      · linarith only [h0, h318, h324, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h2, h321, h322, h324, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h316, h317, h319, h321, h4, hc34, hlam, hphi, u3ehi2]
              · linarith only [h0, h3, h317, h318, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h329 | h329
              · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
                · linarith only [h1, h330, h4, hlam]
                · linarith only [h317, h329, h330, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h333 | h333
                · linarith only [h1, h333, h4, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h335 | h335
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                    · linarith only [h3, h336, h4, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h338 | h338
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h339 | h339
                        · rcases h4bigk with h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h335, hc04, hlam, hphi, ht0b, ht45, ht5b, p340_1, u4ehi4]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h329, h4, hc12, hc34, hlam, hphi, ht23, p340_1]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h4, hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            rcases p340_3 (m.d 0 4) (by simp) with h345 | h345
                            · rcases p340_3 (m.d 1 4) (by simp) with h346 | h346
                              · linarith only [h2, h346, hlam]
                              · linarith only [h335, h346, hlam]
                            · linarith only [h345, hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h2, hlam, p340_1]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h329, hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h333, hlam, p340_1]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p340_1, u4ehi4]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h3, hlam, p340_1]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p340_1, u4ehi1]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h336, hlam, p340_1]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p340_1, u4ehi4]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h2, h335, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p340_1, u4ehi4]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h335, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p340_1, u4ehi4]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h329, h335, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p340_1, u4ehi4]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            rcases p340_3 (m.d 0 4) (by simp) with h364 | h364
                            · linarith only [h364, h4, hlam]
                            · linarith only [h316, h364, hlam]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h316, hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h335, hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h338, hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [h339, hlam, p340_0]
                          · have p340_0 := h340c.1
                            have p340_1 := h340c.2.1
                            have p340_2 := h340c.2.2.1
                            have p340_3 := h340c.2.2.2
                            linarith only [hlam, p340_0]
                        · linarith only [h2, h335, h339, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h329, h335, h338, hlam]
                  · linarith only [h316, h333, h335, h4, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h375 | h375
            · rcases m.htr 1 2 4 (by decide) (by decide) with h376 | h376
              · rcases m.htr 1 3 4 (by decide) (by decide) with h377 | h377
                · linarith only [h1, h377, h4, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h379 | h379
                  · linarith only [h2, h316, h379, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h381 | h381
                    · linarith only [h1, h316, h375, h381, h4, hc45, hlam, hphi, u4ehi3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
                      · linarith only [h0, h316, h376, h383, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h385 | h385
                        · linarith only [h1, h316, h375, h385, h4, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1, h375, h385, h4, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h3, h375, h376, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h389 | h389
              · linarith only [h1, h316, h375, h389, h4, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
                · linarith only [h1, h391, h4, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                  · linarith only [h3, h316, h389, h393, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h395 | h395
                    · linarith only [h3, h316, h395, h4, hc45, hlam, hphi, ht34, u3ehi0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h397 | h397
                      · linarith only [h3, h316, h397, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h399 | h399
                        · linarith only [h3, h316, h389, h391, h399, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h1, h399, h4, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h402 | h402
      · rcases m.htr 0 3 5 (by decide) (by decide) with h403 | h403
        · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
          · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
            · rcases m.htr 1 2 4 (by decide) (by decide) with h406 | h406
              · linarith only [h0, h3, h406, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                · linarith only [h405, h406, h408, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                    · linarith only [h0, h405, h408, h411, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h0, h3, h402, h405, h411, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h405, h406, h410, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h415 | h415
              · linarith only [h0, h3, h415, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h417 | h417
                · rcases m.htr 1 4 5 (by decide) (by decide) with h418 | h418
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h420 | h420
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h421 | h421
                        · linarith only [h1, h417, h421, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h2, h418, h421, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h3, h417, h418, h420, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h402, h405, h417, h418, h419, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h426 | h426
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h427 | h427
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h428 | h428
                        · linarith only [h417, h418, h428, hlam]
                        · rcases h4bigk with h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c | h430c
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            rcases p430_3 (m.d 0 4) (by simp) with h432 | h432
                            · rcases p430_3 (m.d 1 4) (by simp) with h433 | h433
                              · linarith only [h2, h433, hlam]
                              · rcases p430_3 (m.d 2 4) (by simp) with h435 | h435
                                · rcases p430_3 (m.d 3 4) (by simp) with h436 | h436
                                  · linarith only [h402, h436, hlam]
                                  · rcases p430_3 (m.d 4 5) (by simp) with h438 | h438
                                    · linarith only [h404, h438, hlam]
                                    · linarith only [h418, h438, hlam]
                                · linarith only [h415, h435, hlam]
                            · linarith only [h2, h432, hlam]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h3, hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            rcases p430_3 (m.d 0 4) (by simp) with h444 | h444
                            · rcases p430_3 (m.d 1 4) (by simp) with h445 | h445
                              · linarith only [h2, h445, hlam]
                              · linarith only [h417, h445, hlam]
                            · linarith only [h402, h444, hlam]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h3, h417, h418, h426, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p430_1, u3ehi3]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h2, hlam, p430_1]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h415, hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h404, h418, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p430_1, u3ehi3]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h418, hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h404, h426, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p430_1, u4ehi4]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            rcases p430_3 (m.d 0 4) (by simp) with h456 | h456
                            · linarith only [h3, h456, hlam]
                            · linarith only [h2, h456, hlam]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            rcases p430_3 (m.d 0 4) (by simp) with h460 | h460
                            · linarith only [h3, h460, hlam]
                            · linarith only [h402, h460, hlam]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h417, h418, h426, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p430_1, u3ehi3]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h402, hlam, p430_1]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h417, hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h426, hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h428, hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h404, hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h404, h417, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p430_1, u3ehi3]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h427, hlam, p430_0]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [h3, h404, h426, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p430_1, u3ehi3]
                          · have p430_0 := h430c.1
                            have p430_1 := h430c.2.1
                            have p430_2 := h430c.2.2.1
                            have p430_3 := h430c.2.2.2
                            linarith only [hlam, p430_0]
                      · linarith only [h3, h404, h427, hlam]
                    · linarith only [h1, h417, h426, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h479 | h479
                        · rcases h4bigk with h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c | h480c
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h3, h476, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p480_1, u4ehi4]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h3, hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h3, h417, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p480_1, u3ehi1]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            rcases p480_3 (m.d 0 4) (by simp) with h485 | h485
                            · rcases p480_3 (m.d 1 4) (by simp) with h486 | h486
                              · linarith only [h2, h486, hlam]
                              · linarith only [h476, h486, hlam]
                            · linarith only [h485, hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h2, hlam, p480_1]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h415, hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h417, hlam, p480_1]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p480_1, u4ehi4]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h402, h417, h477, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p480_1, u3ehi1]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h476, h477, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p480_1, u4ehi4]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h417, h477, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p480_1, u3ehi1]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            rcases p480_3 (m.d 0 4) (by simp) with h499 | h499
                            · linarith only [h3, h499, hlam]
                            · linarith only [h404, h499, hlam]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h402, hlam, p480_1]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h402, h476, hc04, hlam, hphi, ht0b, ht45, ht5b, p480_1, u4ehi4]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h477, hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h477, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p480_1, u4ehi4]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h404, hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h476, hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h478, hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [h479, hlam, p480_0]
                          · have p480_0 := h480c.1
                            have p480_1 := h480c.2.1
                            have p480_2 := h480c.2.2.1
                            have p480_3 := h480c.2.2.2
                            linarith only [hlam, p480_0]
                        · linarith only [h2, h476, h479, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h3, h417, h476, h477, h478, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · linarith only [h3, h402, h477, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h515 | h515
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h516 | h516
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h517 | h517
                        · linarith only [h417, h476, h517, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h3, h404, h417, h515, h517, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h3, h404, h516, hlam]
                    · linarith only [h3, h402, h515, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
            · linarith only [h0, h3, h404, h522, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
              · linarith only [h0, h3, h524, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
                · rcases m.htr 1 4 5 (by decide) (by decide) with h527 | h527
                  · linarith only [h2, h404, h527, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h529 | h529
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h530 | h530
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h531 | h531
                        · linarith only [h1, h404, h526, h531, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                        · rcases h4bigk with h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h404, h526, h529, h530, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p533_1, u3ehi3]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h3, hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h404, h529, h530, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p533_1, u3ehi3]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h404, hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h2, hlam, p533_1]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h524, hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p533_1, u3ehi3]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h527, hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            rcases p533_3 (m.d 0 4) (by simp) with h544 | h544
                            · linarith only [h3, h544, hlam]
                            · rcases p533_3 (m.d 1 4) (by simp) with h546 | h546
                              · linarith only [h524, h546, hlam]
                              · rcases p533_3 (m.d 2 4) (by simp) with h548 | h548
                                · rcases p533_3 (m.d 3 4) (by simp) with h549 | h549
                                  · linarith only [h529, h549, hlam]
                                  · rcases p533_3 (m.d 4 5) (by simp) with h551 | h551
                                    · linarith only [h530, h551, hlam]
                                    · linarith only [h404, h551, hlam]
                                · linarith only [h3, h548, hlam]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            rcases p533_3 (m.d 0 4) (by simp) with h555 | h555
                            · linarith only [h3, h555, hlam]
                            · linarith only [h2, h555, hlam]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            rcases p533_3 (m.d 0 4) (by simp) with h559 | h559
                            · linarith only [h3, h559, hlam]
                            · linarith only [h402, h559, hlam]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h404, h529, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p533_1, u4ehi0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h402, hlam, p533_1]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h526, hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h529, hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h531, hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, p533_1, u4ehi1]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h526, hc45, hlam, hphi, ht34, p533_1, u3ehi3]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h530, hlam, p533_0]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [h529, h530, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p533_1, u3ehi3]
                          · have p533_0 := h533c.1
                            have p533_1 := h533c.2.1
                            have p533_2 := h533c.2.2.1
                            have p533_3 := h533c.2.2.2
                            linarith only [hlam, p533_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                        · linarith only [h2, h526, h530, h573, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · rcases h4bigk with h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c | h575c
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h3, h530, hc45, hlam, hphi, p575_1, u4ehi1]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h3, hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h3, h530, hc45, hlam, hphi, ht34, p575_1, u3ehi3]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h404, hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h2, hlam, p575_1]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h524, hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p575_1, u3ehi3]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h527, hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h530, hc45, hlam, hphi, p575_1, u4ehi0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h530, hc45, hlam, hphi, p575_1, u4ehi1]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h530, hc45, hlam, hphi, ht34, p575_1, u3ehi3]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h530, hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h402, hlam, p575_1]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h526, hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h529, hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h573, hlam, p575_0]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h2, h526, hc45, hlam, hphi, ht34, p575_1, u3ehi3]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [h526, hc45, hlam, hphi, ht34, p575_1, u3ehi3]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [hc45, hlam, hphi, p575_1, u4ehi2]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p575_1, u3ehi3]
                          · have p575_0 := h575c.1
                            have p575_1 := h575c.2.1
                            have p575_2 := h575c.2.2.1
                            have p575_3 := h575c.2.2.2
                            linarith only [hlam, p575_0]
                    · linarith only [h1, h526, h529, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h402, h404, h526, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h402, h403, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h604 | h604
        · linarith only [h402, h604, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h606 | h606
          · rcases m.htr 1 2 3 (by decide) (by decide) with h607 | h607
            · rcases m.htr 1 2 4 (by decide) (by decide) with h608 | h608
              · linarith only [h0, h3, h608, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h610 | h610
                · linarith only [h1, h402, h610, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h612 | h612
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                    · linarith only [h0, h3, h402, h607, h613, hlam]
                    · linarith only [h0, h3, h607, h613, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h607, h608, h612, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h617 | h617
              · linarith only [h3, h607, h617, hc02, hc23, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h619 | h619
                · linarith only [h1, h604, h619, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h621 | h621
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h622 | h622
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h623 | h623
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h624 | h624
                        · rcases h4bigk with h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c | h625c
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h621, hc04, hlam, hphi, ht0b, ht45, ht5b, p625_1, u4ehi4]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h3, hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h402, hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h402, h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p625_1, u4ehi4]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h2, hlam, p625_1]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h617, hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h619, hlam, p625_1]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p625_1, u4ehi4]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h606, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p625_1, u4ehi4]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h621, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p625_1, u4ehi4]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h604, h622, h624, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p625_1, u3ehi0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            rcases p625_3 (m.d 0 4) (by simp) with h640 | h640
                            · linarith only [h3, h640, hlam]
                            · linarith only [h606, h640, hlam]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h2, h621, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p625_1, u4ehi4]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h621, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p625_1, u4ehi4]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h622, hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h622, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p625_1, u4ehi4]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h606, hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h621, hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h623, hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [h624, hlam, p625_0]
                          · have p625_0 := h625c.1
                            have p625_1 := h625c.2.1
                            have p625_2 := h625c.2.2.1
                            have p625_3 := h625c.2.2.2
                            linarith only [hlam, p625_0]
                        · linarith only [h1, h2, h402, h621, h624, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h2, h402, h621, h622, h623, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h655 | h655
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h656 | h656
                        · rcases h4bigk with h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c | h657c
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h621, hc04, hlam, hphi, ht0b, ht45, ht5b, p657_1, u4ehi4]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h3, hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h402, hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            rcases p657_3 (m.d 0 4) (by simp) with h662 | h662
                            · rcases p657_3 (m.d 1 4) (by simp) with h663 | h663
                              · linarith only [h2, h663, hlam]
                              · linarith only [h621, h663, hlam]
                            · linarith only [h662, hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h2, hlam, p657_1]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h617, hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h619, hlam, p657_1]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht45, ht5b, p657_1, u4ehi4]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h402, h622, hc34, hlam, hphi, p657_1, u3ehi0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h619, h622, hc34, hlam, hphi, p657_1, u3ehi1]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h622, hlam, p657_1]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            rcases p657_3 (m.d 0 4) (by simp) with h676 | h676
                            · linarith only [h3, h676, hlam]
                            · linarith only [h606, h676, hlam]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h2, h621, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p657_1, u4ehi4]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h621, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p657_1, u4ehi4]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h3, hc02, hc34, hlam, hphi, ht23, p657_1]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            rcases p657_3 (m.d 0 4) (by simp) with h683 | h683
                            · linarith only [h402, h683, hlam]
                            · linarith only [h606, h683, hlam]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h606, hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h621, hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h655, hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [h656, hlam, p657_0]
                          · have p657_0 := h657c.1
                            have p657_1 := h657c.2.1
                            have p657_2 := h657c.2.2.1
                            have p657_3 := h657c.2.2.2
                            linarith only [hlam, p657_0]
                        · linarith only [h2, h621, h656, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h2, h3, h621, h655, hlam]
                  · linarith only [h402, h606, h619, h621, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h694 | h694
            · linarith only [h0, h3, h606, h694, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h696 | h696
              · linarith only [h0, h3, h606, h696, hc45, hlam, hphi, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h698 | h698
                · linarith only [h1, h402, h606, h698, hc45, hlam, hphi, u4ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h700 | h700
                  · linarith only [h2, h402, h606, h700, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h702 | h702
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h703 | h703
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h704 | h704
                        · linarith only [h1, h402, h606, h704, hc34, hlam, hphi, u3ehi1]
                        · linarith only [h1, h402, h702, h703, h704, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1, h402, h702, h703, hc45, hlam, hphi, ht34, u3ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h708 | h708
                      · linarith only [h1, h402, h606, h702, h708, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h710 | h710
                        · linarith only [h0, h3, h708, h710, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1, h402, h710, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h713 | h713
    · linarith only [h0, h2, h713, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h715 | h715
      · linarith only [h1, h2, h715, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h717 | h717
        · linarith only [h715, h717, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h719 | h719
          · rcases m.htr 1 2 3 (by decide) (by decide) with h720 | h720
            · linarith only [h0, h2, h720, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h722 | h722
              · linarith only [h1, h2, h713, h720, h722, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h724 | h724
                · linarith only [h1, h2, h715, h722, h724, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h1, h2, h724, hc34, hlam, hphi, u3ehi1]
          · linarith only [h1, h2, h719, hc45, hlam, hphi, ht34, u3ehi1]

end R2N4
