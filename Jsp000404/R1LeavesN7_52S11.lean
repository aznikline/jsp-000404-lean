import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5150000 in
set_option maxHeartbeats 5150000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_R_L_R_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
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
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                            · linarith only [h0, h10, h15, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h10, h13, h15, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h13, h14, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h0, h13, h19, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                            · linarith only [h10, h13, h21, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                              · linarith only [h0, h10, h13, h19, h23, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                                · linarith only [h0, h11, h25, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                                  · linarith only [h0, h21, h25, h27, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                  · linarith only [h13, h27, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h10, h11, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h33 | h33
                      · linarith only [h0, h10, h33, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                            · linarith only [h0, h32, h33, h37, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h10, h36, h37, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h35, h36, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h10, h32, h35, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h32, h42, h5, hc02, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h44 | h44
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h45 | h45
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h48 | h48
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                                  · linarith only [h1, h44, h49, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h0, h4, h46, h48, h49, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                                  · linarith only [h1, h44, h48, h52, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c | h54c
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h10, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi1]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h32, h44, h48, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h32, h44, h48, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h32, h44, h48, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h0, hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h32, h44, h48, h7, h9, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h0, h32, h44, h48, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h0, h32, h44, h48, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h1, hlam, p54_1]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h4, hlam, p54_1]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h32, h44, h48, h9, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h0, h32, h4, h44, h48, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h2, hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h5, hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h7, hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h32, h44, h48, h9, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p54_1, u3ehi3]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h3, hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h6, hlam, p54_1]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h8, hlam, p54_0]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [h9, hlam, p54_1]
                                    · have p54_0 := h54c.1
                                      have p54_1 := h54c.2.1
                                      have p54_2 := h54c.2.2.1
                                      have p54_3 := h54c.2.2.2
                                      linarith only [hlam, p54_0]
                              · linarith only [h10, h45, h47, hlam]
                            · linarith only [h10, h44, h46, hlam]
                          · linarith only [h44, h45, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h83 | h83
                          · linarith only [h0, h4, h44, h7, h83, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                            · linarith only [h0, h4, h44, h85, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h87 | h87
                              · linarith only [h83, h85, h87, hc34, hlam, hphi, u3ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h90 | h90
                                  · rcases h0bigk with h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c | h91c
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi3]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h2, h44, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h10, h8, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h0, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h7, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi3]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h0, h2, h44, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p91_1, u3ehi1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h0, h10, h8, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h1, hlam, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h4, hlam, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h5, h89, hc03, hlam, hphi, ht0b, ht5b, p91_1, u5ehi4]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h0, h10, h4, h8, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h2, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h5, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h7, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h10, h8, h87, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h3, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h6, hlam, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h8, hlam, p91_0]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [h9, hlam, p91_1]
                                    · have p91_0 := h91c.1
                                      have p91_1 := h91c.2.1
                                      have p91_2 := h91c.2.2.1
                                      have p91_3 := h91c.2.2.2
                                      linarith only [hlam, p91_0]
                                  · linarith only [h10, h85, h89, h90, hc12, hc24, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h118 | h118
                                  · linarith only [h0, h118, h32, h4, h44, h7, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h118, h44, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h122 | h122
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h123 | h123
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                            · linarith only [h0, h121, h126, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h124, h126, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h0, h124, h125, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h124, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h0, h121, h123, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h121, h122, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                      · linarith only [h0, h121, h134, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                            · linarith only [h0, h121, h133, h138, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h121, h133, h136, h138, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h136, h137, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h136, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h143 | h143
                      · linarith only [h133, h143, h5, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h149 | h149
                                · linarith only [h149, h5, h9, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
                                  · linarith only [h133, h145, h151, h5, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                  · rcases h0bigk with h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c | h153c
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1, u3ehi0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1, u3ehi0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h133, h145, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1, u3ehi3]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht5b, p153_1, u5ehi0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h0, hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1, u3ehi1]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h0, h133, h145, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1, u3ehi3]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h0, h146, h151, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1, u3ehi3]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h1, hlam, p153_1]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h4, hlam, p153_1]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h133, h145, h5, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1, u3ehi3]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h0, h133, h145, h149, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1, u3ehi3]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h2, hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h5, hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h7, hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h9, hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h3, hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h6, hlam, p153_1]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h8, hlam, p153_0]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [h133, h145, h5, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p153_1, u3ehi3]
                                    · have p153_0 := h153c.1
                                      have p153_1 := h153c.2.1
                                      have p153_2 := h153c.2.2.1
                                      have p153_3 := h153c.2.2.2
                                      linarith only [hlam, p153_0]
                              · linarith only [h121, h146, h148, hlam]
                            · linarith only [h121, h145, h147, hlam]
                          · linarith only [h145, h146, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h145, h7, h9, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h184 | h184
              · linarith only [h184, h7, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h186 | h186
                · rcases m.htr 1 2 3 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h189 | h189
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
                        · linarith only [h1, h190, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
                          · linarith only [h1, h184, h192, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                            · linarith only [h187, h194, h7, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h196 | h196
                              · linarith only [h1, h184, h187, h196, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h198 | h198
                                · linarith only [h0, h188, h198, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                · linarith only [h186, h194, h198, h7, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h0, h187, h189, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h187, h188, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h187, h204, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                        · linarith only [h187, h206, h4, h7, hlam]
                        · linarith only [h187, h203, h206, h4, h7, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h209 | h209
                      · linarith only [h0, h203, h209, h5, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
                        · linarith only [h1, h211, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h213 | h213
                          · linarith only [h1, h184, h187, h213, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
                            · linarith only [h215, h4, h7, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h217 | h217
                              · linarith only [h184, h217, h4, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h219 | h219
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h220 | h220
                                  · rcases h0bigk with h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c | h221c
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [hlam, p221_0]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h187, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h187, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h219, h5, hc01, hlam, hphi, ht0b, ht5b, p221_1, u5ehi4]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h184, h187, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h0, hlam, p221_0]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [hlam, p221_0]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h187, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h0, h219, h5, hc01, hlam, hphi, ht0b, ht5b, p221_1, u5ehi4]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h0, h184, h187, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h1, hlam, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h4, hlam, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [hlam, p221_0]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h7, hlam, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h184, hlam, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h2, hlam, p221_0]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h5, hlam, p221_0]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h187, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [hlam, p221_0]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h184, h187, h4, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h3, hlam, p221_0]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h6, hlam, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h187, h4, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [h186, hlam, p221_1]
                                    · have p221_0 := h221c.1
                                      have p221_1 := h221c.2.1
                                      have p221_2 := h221c.2.2.1
                                      have p221_3 := h221c.2.2.2
                                      linarith only [hlam, p221_0]
                                  · linarith only [h0, h2, h211, h219, h220, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                · linarith only [h186, h203, h219, h7, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h251 | h251
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h252 | h252
                        · linarith only [h1, h252, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
                          · linarith only [h1, h186, h254, h7, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                            · linarith only [h0, h249, h256, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h258 | h258
                              · linarith only [h1, h186, h249, h258, h7, hc45, hlam, hphi, ht34, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h260 | h260
                                · linarith only [h0, h186, h250, h260, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h262 | h262
                                  · linarith only [h1, h186, h249, h262, h7, hc34, hlam, hphi, u3ehi2]
                                  · linarith only [h1, h249, h262, h7, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h0, h249, h251, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h249, h250, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h267 | h267
                    · linarith only [h186, h249, h267, h4, h7, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h269 | h269
                      · linarith only [h186, h249, h269, h4, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h271 | h271
                        · linarith only [h249, h271, h4, h7, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h273 | h273
                          · linarith only [h184, h249, h273, h4, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h275 | h275
                            · linarith only [h275, h4, h7, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h277 | h277
                              · linarith only [h184, h277, h4, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h279 | h279
                                · linarith only [h186, h279, h5, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h281 | h281
                                  · linarith only [h186, h281, h7, hc34, hlam, hphi, u3ehi0]
                                  · linarith only [h249, h281, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
            · rcases m.htr 0 3 5 (by decide) (by decide) with h285 | h285
              · linarith only [h285, h4, h6, hlam]
              · linarith only [h284, h285, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h288 | h288
              · linarith only [h284, h288, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h290 | h290
                · linarith only [h290, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                      · linarith only [h0, h294, h6, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                        · linarith only [h1, h284, h296, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h298 | h298
                          · linarith only [h1, h284, h298, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h300 | h300
                            · linarith only [h0, h284, h292, h300, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h302 | h302
                              · linarith only [h1, h284, h292, h302, hc34, hlam, hphi, u3ehi4]
                              · linarith only [h0, h293, h300, h302, h6, hc35, hlam, hphi, u3ehi2]
                    · linarith only [h293, h5, h6, hc12, hc25, hlam, hphi]
                  · linarith only [h292, h4, h6, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h307 | h307
          · rcases m.htr 0 3 4 (by decide) (by decide) with h308 | h308
            · linarith only [h308, h4, h5, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h310 | h310
              · linarith only [h308, h310, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
                · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h314 | h314
                    · linarith only [h307, h314, h5, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h317 | h317
                        · linarith only [h1, h308, h317, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h319 | h319
                          · linarith only [h1, h310, h319, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
                            · linarith only [h0, h308, h313, h321, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h321, h4, h5, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h307, h313, h316, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h313, h4, h5, hc12, hc24, hlam, hphi]
                · linarith only [h312, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h327 | h327
            · linarith only [h327, h4, h5, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h329 | h329
              · linarith only [h327, h329, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
                · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h333 | h333
                    · linarith only [h0, h333, h5, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h335 | h335
                      · linarith only [h0, h307, h335, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h337 | h337
                        · linarith only [h1, h327, h337, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h339 | h339
                          · linarith only [h1, h327, h339, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h341 | h341
                            · linarith only [h0, h327, h332, h341, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h341, h4, h5, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h332, h4, h5, hc12, hc24, hlam, hphi]
                · linarith only [h331, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h346 | h346
        · rcases m.htr 0 2 5 (by decide) (by decide) with h347 | h347
          · rcases m.htr 0 3 4 (by decide) (by decide) with h348 | h348
            · rcases m.htr 0 3 5 (by decide) (by decide) with h349 | h349
              · rcases m.htr 0 4 5 (by decide) (by decide) with h350 | h350
                · rcases m.htr 1 2 3 (by decide) (by decide) with h351 | h351
                  · linarith only [h347, h351, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h353 | h353
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h354 | h354
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h356 | h356
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h358 | h358
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h359 | h359
                                · linarith only [h0, h353, h359, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                                · linarith only [h346, h350, h357, h359, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h346, h357, h358, h4, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h1, h346, h350, h355, h357, h4, hc03, hlam, hphi, ht0b, ht5b, u5ehi4]
                          · linarith only [h355, h356, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h346, h348, h351, h354, h355, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h347, h354, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h346, h353, h4, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
                  · linarith only [h347, h368, h4, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h370 | h370
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h374 | h374
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h375 | h375
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h376 | h376
                                · linarith only [h0, h350, h370, h376, h4, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h378 | h378
                                  · linarith only [h2, h350, h370, h374, h378, hlam]
                                  · rcases h0bigk with h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h0, h371, h374, h376, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p380_1, u3ehi3]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p380_1, u3ehi0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h2, h370, h374, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p380_1, u3ehi3]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht5b, p380_1, u5ehi0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h0, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h4, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h2, h370, h374, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p380_1, u3ehi3]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h3, hc02, hlam, hphi, ht0b, ht5b, p380_1, u5ehi1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h1, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h0, h371, h374, h376, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p380_1, u3ehi3]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h2, h370, h374, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p380_1, u3ehi3]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h347, h374, h376, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p380_1, u3ehi3]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h2, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h346, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h348, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h350, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h3, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h347, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h349, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h2, h370, h374, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p380_1, u3ehi3]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                              · linarith only [h0, h371, h375, h4, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                            · linarith only [h0, h371, h372, h374, h4, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                          · linarith only [h347, h349, h368, h371, h373, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                        · linarith only [h348, h368, h371, h372, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h347, h371, h4, hc12, hc23, hlam, hphi]
                    · linarith only [h346, h370, h4, hc12, hc23, hlam, hphi]
              · linarith only [h348, h349, hc35, hlam, hphi, u3ehi3]
            · linarith only [h346, h348, h4, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h414 | h414
            · rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
              · rcases m.htr 0 4 5 (by decide) (by decide) with h416 | h416
                · linarith only [h346, h347, h416, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h418 | h418
                  · linarith only [h0, h4, h418, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h421 | h421
                      · linarith only [h0, h347, h421, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h423 | h423
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h424 | h424
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h425 | h425
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h426 | h426
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h427 | h427
                                · linarith only [h0, h347, h416, h420, h426, h427, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h347, h420, h425, h427, hc45, hlam, hphi, ht34, u3ehi3]
                              · linarith only [h1, h424, h426, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h1, h4, h424, h425, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h423, h424, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h414, h416, h423, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h346, h347, h420, hc12, hc25, hlam, hphi]
              · linarith only [h414, h415, hc35, hlam, hphi, u3ehi3]
            · linarith only [h346, h4, h414, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h437 | h437
          · rcases m.htr 0 3 4 (by decide) (by decide) with h438 | h438
            · rcases m.htr 0 3 5 (by decide) (by decide) with h439 | h439
              · rcases m.htr 0 4 5 (by decide) (by decide) with h440 | h440
                · rcases m.htr 1 2 3 (by decide) (by decide) with h441 | h441
                  · linarith only [h0, h4, h441, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h443 | h443
                    · linarith only [h0, h346, h443, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h445 | h445
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h446 | h446
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h447 | h447
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h449 | h449
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h450 | h450
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h451 | h451
                                  · linarith only [h1, h446, h451, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · linarith only [h0, h445, h450, h451, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h346, h445, h450, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                              · linarith only [h0, h3, h346, h445, h447, h448, h449, hc05, hlam, hphi, ht0b, ht5b, u5ehi2]
                            · linarith only [h0, h4, h445, h448, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                          · linarith only [h446, h447, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h438, h441, h445, h446, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · linarith only [h346, h437, h445, hc12, hc24, hlam, hphi]
                · linarith only [h346, h437, h440, hlam]
              · linarith only [h438, h439, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h462 | h462
              · linarith only [h438, h462, hc34, hlam, hphi, u3ehi4]
              · linarith only [h4, h437, h462, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h465 | h465
            · rcases m.htr 0 3 5 (by decide) (by decide) with h466 | h466
              · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
                · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                  · linarith only [h0, h4, h466, h468, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h470 | h470
                    · linarith only [h0, h346, h470, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                      · linarith only [h0, h437, h472, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h474 | h474
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h475 | h475
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h476 | h476
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h477 | h477
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h479 | h479
                                  · linarith only [h1, h474, h479, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                                  · rcases h0bigk with h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      rcases p481_3 (m.d 0 1) (by simp) with h483 | h483
                                      · rcases p481_3 (m.d 0 2) (by simp) with h484 | h484
                                        · linarith only [h0, h484, hlam]
                                        · rcases p481_3 (m.d 0 3) (by simp) with h486 | h486
                                          · linarith only [h1, h486, hlam]
                                          · linarith only [h4, h486, hlam]
                                      · linarith only [h0, h483, hlam]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h465, h467, h479, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1, u3ehi3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h467, h479, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1, u3ehi3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h467, h479, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p481_1, u3ehi3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h4, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h346, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h437, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h1, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h4, hc02, hc23, hlam, hphi, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h4, h467, h479, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p481_1, u3ehi3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h4, h467, h479, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p481_1, u3ehi3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h2, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, h346, hc12, hc24, hlam, hphi, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h465, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h4, h465, h467, h479, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p481_1, u3ehi3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h3, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h0, h437, hc12, hc25, hlam, hphi, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h466, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h467, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                · linarith only [h346, h467, h478, hlam]
                              · linarith only [h1, h4, h475, h477, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                            · linarith only [h4, h465, h476, hlam]
                          · linarith only [h466, h474, h475, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h517 | h517
                          · linarith only [h474, h517, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h520 | h520
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h521 | h521
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h522 | h522
                                  · rcases h0bigk with h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      rcases p523_3 (m.d 0 1) (by simp) with h525 | h525
                                      · rcases p523_3 (m.d 0 2) (by simp) with h526 | h526
                                        · linarith only [h0, h526, hlam]
                                        · rcases p523_3 (m.d 0 3) (by simp) with h528 | h528
                                          · linarith only [h1, h528, hlam]
                                          · linarith only [h4, h528, hlam]
                                      · linarith only [h0, h525, hlam]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p523_1, u3ehi0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h467, hc01, hlam, hphi, ht0b, ht5b, p523_1, u5ehi0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht5b, p523_1, u5ehi0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h0, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h4, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h346, hlam, p523_1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h437, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h1, hlam, p523_1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p523_1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h3, h4, h467, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p523_1, u5ehi1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p523_1, u5ehi1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h2, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h0, h346, h519, hc12, hc23, hlam, hphi, p523_1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h465, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h346, h466, h519, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p523_1, u3ehi4]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h3, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h0, h437, h519, h521, hc12, hc23, hlam, hphi, p523_1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h466, hlam, p523_0]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [h467, hlam, p523_1]
                                    · have p523_0 := h523c.1
                                      have p523_1 := h523c.2.1
                                      have p523_2 := h523c.2.2.1
                                      have p523_3 := h523c.2.2.2
                                      linarith only [hlam, p523_0]
                                  · linarith only [h474, h522, hc45, hlam, hphi, ht34, u3ehi1]
                                · linarith only [h346, h467, h521, hlam]
                              · linarith only [h4, h465, h474, h520, hc35, hlam, hphi, u3ehi1]
                            · linarith only [h4, h465, h519, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h559 | h559
                  · linarith only [h0, h4, h559, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h561 | h561
                    · linarith only [h0, h346, h561, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h563 | h563
                      · linarith only [h0, h437, h563, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h565 | h565
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h566 | h566
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h567 | h567
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h568 | h568
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h569 | h569
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                                  · linarith only [h2, h467, h565, h570, hlam]
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
                                      rcases p572_3 (m.d 0 1) (by simp) with h574 | h574
                                      · rcases p572_3 (m.d 0 2) (by simp) with h575 | h575
                                        · linarith only [h0, h575, hlam]
                                        · rcases p572_3 (m.d 0 3) (by simp) with h577 | h577
                                          · linarith only [h1, h577, hlam]
                                          · linarith only [h4, h577, hlam]
                                      · linarith only [h0, h574, hlam]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h1, h566, h570, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1, u3ehi3]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h2, h565, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1, u3ehi3]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h2, h467, h565, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p572_1, u3ehi3]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h0, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h4, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h346, hlam, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h437, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h1, hlam, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h2, h4, h565, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p572_1, u3ehi3]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h2, h4, h467, h565, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p572_1, u3ehi3]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h2, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h0, h467, h569, hc12, hc24, hlam, hphi, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h465, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h467, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h3, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h0, h437, hc12, hc25, hlam, hphi, p572_1]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h466, hlam, p572_0]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [h465, h467, h569, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p572_1, u3ehi3]
                                    · have p572_0 := h572c.1
                                      have p572_1 := h572c.2.1
                                      have p572_2 := h572c.2.2.1
                                      have p572_3 := h572c.2.2.2
                                      linarith only [hlam, p572_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h604 | h604
                                  · linarith only [h0, h346, h569, h604, hc12, hc34, hlam, hphi, ht23]
                                  · rcases h0bigk with h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      rcases p606_3 (m.d 0 1) (by simp) with h608 | h608
                                      · rcases p606_3 (m.d 0 2) (by simp) with h609 | h609
                                        · linarith only [h0, h609, hlam]
                                        · rcases p606_3 (m.d 0 3) (by simp) with h611 | h611
                                          · linarith only [h1, h611, hlam]
                                          · linarith only [h4, h611, hlam]
                                      · linarith only [h0, h608, hlam]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p606_1, u3ehi0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h2, h565, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p606_1, u3ehi3]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht5b, p606_1, u5ehi0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h0, hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h4, hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h346, hlam, p606_1]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h437, hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h1, hlam, p606_1]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h0, h4, hc12, hc23, hlam, hphi, p606_1]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h2, h4, h565, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p606_1, u3ehi3]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h3, h4, h566, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p606_1, u3ehi4]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h2, hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h0, h346, hc12, hc24, hlam, hphi, p606_1]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h465, hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h467, hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h3, hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h0, h437, hc12, hc25, hlam, hphi, p606_1]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h466, hlam, p606_0]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [h467, hc04, hc45, hlam, hphi, p606_1]
                                    · have p606_0 := h606c.1
                                      have p606_1 := h606c.2.1
                                      have p606_2 := h606c.2.2.1
                                      have p606_3 := h606c.2.2.2
                                      linarith only [hlam, p606_0]
                              · linarith only [h4, h465, h568, hc35, hlam, hphi, u3ehi3]
                            · linarith only [h1, h4, h565, h567, hlam]
                          · linarith only [h565, h566, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h465, h467, h565, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h465, h466, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h643 | h643
              · linarith only [h465, h643, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h645 | h645
                · rcases m.htr 1 2 3 (by decide) (by decide) with h646 | h646
                  · linarith only [h0, h4, h646, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h648 | h648
                    · linarith only [h0, h346, h4, h645, h648, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h650 | h650
                      · linarith only [h0, h437, h650, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h652 | h652
                        · linarith only [h1, h465, h652, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h654 | h654
                          · linarith only [h1, h643, h654, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h656 | h656
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h657 | h657
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h658 | h658
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h659 | h659
                                  · rcases h0bigk with h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c | h660c
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [hlam, p660_0]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      rcases p660_3 (m.d 0 1) (by simp) with h662 | h662
                                      · rcases p660_3 (m.d 0 2) (by simp) with h663 | h663
                                        · linarith only [h0, h663, hlam]
                                        · rcases p660_3 (m.d 0 3) (by simp) with h665 | h665
                                          · linarith only [h1, h665, hlam]
                                          · linarith only [h4, h665, hlam]
                                      · linarith only [h0, h662, hlam]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p660_1, u3ehi1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h645, hc01, hlam, hphi, ht0b, ht5b, p660_1, u5ehi4]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h1, h643, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p660_1, u3ehi1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h0, hlam, p660_0]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [hlam, p660_0]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h4, hlam, p660_0]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h346, hlam, p660_1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h437, hlam, p660_0]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h1, hlam, p660_1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h0, h643, h656, h659, hc12, hc23, hlam, hphi, p660_1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [hlam, p660_0]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h465, hlam, p660_1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h643, hlam, p660_1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h2, hlam, p660_0]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h0, h346, hc12, hc24, hlam, hphi, p660_1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h1, h465, h656, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p660_1, u3ehi1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [hlam, p660_0]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h1, h465, h643, h656, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p660_1, u3ehi1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h3, hlam, p660_0]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h0, h437, hc12, hc25, hlam, hphi, p660_1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h1, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p660_1, u3ehi1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [h645, hlam, p660_1]
                                    · have p660_0 := h660c.1
                                      have p660_1 := h660c.2.1
                                      have p660_2 := h660c.2.2.1
                                      have p660_3 := h660c.2.2.2
                                      linarith only [hlam, p660_0]
                                  · linarith only [h1, h465, h659, hc45, hlam, hphi, ht34, u3ehi1]
                                · linarith only [h0, h346, h465, h645, h656, h658, hc12, hc23, hlam, hphi]
                              · linarith only [h1, h465, h656, h657, hc35, hlam, hphi, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h695 | h695
                              · linarith only [h656, h695, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h697 | h697
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h698 | h698
                                  · rcases h0bigk with h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c | h699c
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [hlam, p699_0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      rcases p699_3 (m.d 0 1) (by simp) with h701 | h701
                                      · rcases p699_3 (m.d 0 2) (by simp) with h702 | h702
                                        · linarith only [h0, h702, hlam]
                                        · rcases p699_3 (m.d 0 3) (by simp) with h704 | h704
                                          · linarith only [h1, h704, hlam]
                                          · linarith only [h4, h704, hlam]
                                      · linarith only [h0, h701, hlam]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p699_1, u3ehi0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h645, hc01, hlam, hphi, ht0b, ht5b, p699_1, u5ehi0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h3, hc01, hlam, hphi, ht0b, ht5b, p699_1, u5ehi1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h0, hlam, p699_0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [hlam, p699_0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h4, hlam, p699_0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h346, hlam, p699_1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h437, hlam, p699_0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h1, hlam, p699_1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h0, h4, h695, h698, hc12, hc34, hlam, hphi, ht23, p699_1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [hlam, p699_0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h465, hlam, p699_1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h643, hlam, p699_1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h2, hlam, p699_0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h0, h346, h656, hc12, hc34, hlam, hphi, ht23, p699_1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h346, h656, hc34, hlam, hphi, p699_1, u3ehi0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [hlam, p699_0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h1, h346, h643, h656, hc34, hlam, hphi, p699_1, u3ehi1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h3, hlam, p699_0]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h0, h437, h656, h697, hc12, hc34, hlam, hphi, ht23, p699_1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h1, h437, h656, h697, hc34, hlam, hphi, p699_1, u3ehi1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [h645, hlam, p699_1]
                                    · have p699_0 := h699c.1
                                      have p699_1 := h699c.2.1
                                      have p699_2 := h699c.2.2.1
                                      have p699_3 := h699c.2.2.2
                                      linarith only [hlam, p699_0]
                                  · linarith only [h1, h465, h698, hc45, hlam, hphi, ht34, u3ehi1]
                                · linarith only [h346, h645, h697, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
                  · linarith only [h0, h4, h733, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
                    · linarith only [h0, h346, h735, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h737 | h737
                      · linarith only [h0, h437, h737, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h739 | h739
                        · linarith only [h1, h465, h645, h739, hc45, hlam, hphi, ht34, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h741 | h741
                          · linarith only [h1, h465, h645, h741, hc45, hlam, hphi, ht34, u3ehi4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h743 | h743
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h744 | h744
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h745 | h745
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h746 | h746
                                  · linarith only [h465, h645, h746, hc34, hlam, hphi, u3ehi0]
                                  · linarith only [h1, h465, h743, h745, h746, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                                · linarith only [h1, h465, h743, h745, hc45, hlam, hphi, ht34, u3ehi1]
                              · linarith only [h1, h465, h743, h744, hc35, hlam, hphi, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h751 | h751
                              · linarith only [h743, h751, hc34, hlam, hphi, u3ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h753 | h753
                                · linarith only [h2, h645, h739, h743, h753, hc34, hlam, hphi, u3ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h755 | h755
                                  · linarith only [h4, h743, h753, h755, hc02, hc34, hlam, hphi, ht23]
                                  · linarith only [h1, h465, h755, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h758 | h758
      · rcases m.htr 0 2 4 (by decide) (by decide) with h759 | h759
        · rcases m.htr 0 2 5 (by decide) (by decide) with h760 | h760
          · linarith only [h0, h3, h760, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h762 | h762
            · rcases m.htr 0 3 5 (by decide) (by decide) with h763 | h763
              · linarith only [h1, h3, h763, hlam]
              · linarith only [h762, h763, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h766 | h766
              · linarith only [h762, h766, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h768 | h768
                · linarith only [h2, h3, h768, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h770 | h770
                  · linarith only [h0, h3, h770, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h758, h760, h770, hc12, hc25, hlam, hphi]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h773 | h773
          · linarith only [h2, h3, h759, h773, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h775 | h775
            · linarith only [h758, h759, h775, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h777 | h777
              · linarith only [h775, h777, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h779 | h779
                · linarith only [h2, h3, h779, hlam]
                · linarith only [h758, h759, h779, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h782 | h782
        · rcases m.htr 0 2 5 (by decide) (by decide) with h783 | h783
          · linarith only [h0, h3, h783, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h785 | h785
            · rcases m.htr 0 3 5 (by decide) (by decide) with h786 | h786
              · linarith only [h1, h3, h786, hlam]
              · linarith only [h785, h786, hc35, hlam, hphi, u3ehi3]
            · linarith only [h758, h782, h785, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h790 | h790
          · linarith only [h0, h3, h790, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h792 | h792
            · rcases m.htr 0 3 5 (by decide) (by decide) with h793 | h793
              · linarith only [h1, h3, h793, hlam]
              · linarith only [h792, h793, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h796 | h796
              · linarith only [h792, h796, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h798 | h798
                · linarith only [h2, h3, h798, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h800 | h800
                  · linarith only [h0, h758, h800, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h802 | h802
                    · linarith only [h0, h782, h802, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h804 | h804
                      · linarith only [h0, h3, h804, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h806 | h806
                        · linarith only [h1, h3, h758, h792, h804, h806, hc02, hc25, hlam, hphi]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h808 | h808
                          · linarith only [h2, h3, h804, h806, h808, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · linarith only [h2, h3, h806, h808, hc35, hlam, hphi, u3ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h811 | h811
    · rcases m.htr 0 2 3 (by decide) (by decide) with h812 | h812
      · rcases m.htr 0 2 4 (by decide) (by decide) with h813 | h813
        · linarith only [h0, h2, h813, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h815 | h815
          · rcases m.htr 0 3 4 (by decide) (by decide) with h816 | h816
            · linarith only [h0, h2, h812, h816, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h818 | h818
              · linarith only [h816, h818, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h820 | h820
                · rcases m.htr 1 2 3 (by decide) (by decide) with h821 | h821
                  · linarith only [h0, h2, h821, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h812, h813, h821, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h820, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h825 | h825
            · linarith only [h2, h811, h812, h815, h825, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h827 | h827
              · linarith only [h825, h827, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h829 | h829
                · rcases m.htr 1 2 3 (by decide) (by decide) with h830 | h830
                  · linarith only [h0, h2, h830, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h812, h813, h830, hc12, hc24, hlam, hphi]
                · linarith only [h1, h2, h829, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h834 | h834
        · linarith only [h0, h2, h834, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h836 | h836
          · rcases m.htr 0 3 4 (by decide) (by decide) with h837 | h837
            · linarith only [h1, h2, h837, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h839 | h839
              · linarith only [h837, h839, hc34, hlam, hphi, u3ehi4]
              · linarith only [h812, h836, h839, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h842 | h842
            · linarith only [h1, h2, h842, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h844 | h844
              · linarith only [h842, h844, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h846 | h846
                · rcases m.htr 1 2 3 (by decide) (by decide) with h847 | h847
                  · linarith only [h0, h2, h812, h847, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h849 | h849
                    · linarith only [h0, h2, h834, h849, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h851 | h851
                      · linarith only [h1, h2, h836, h847, h849, h851, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h853 | h853
                        · linarith only [h1, h2, h849, h853, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h2, h853, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h2, h846, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h857 | h857
      · rcases m.htr 0 2 4 (by decide) (by decide) with h858 | h858
        · linarith only [h0, h2, h858, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h860 | h860
          · linarith only [h0, h811, h860, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h862 | h862
            · linarith only [h0, h2, h857, h862, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h864 | h864
              · linarith only [h862, h864, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h866 | h866
                · rcases m.htr 1 2 3 (by decide) (by decide) with h867 | h867
                  · linarith only [h0, h2, h867, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h857, h858, h867, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h857, h866, hc45, hlam, hphi, ht34, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h871 | h871
        · linarith only [h1, h2, h857, h871, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h873 | h873
          · linarith only [h1, h811, h857, h873, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h875 | h875
            · linarith only [h1, h2, h875, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h877 | h877
              · linarith only [h875, h877, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h879 | h879
                · rcases m.htr 1 2 3 (by decide) (by decide) with h880 | h880
                  · linarith only [h0, h811, h857, h880, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h882 | h882
                    · linarith only [h0, h811, h871, h879, h882, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h884 | h884
                      · linarith only [h1, h2, h873, h880, h882, h884, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h886 | h886
                        · linarith only [h1, h2, h875, h882, h886, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h1, h2, h886, hc34, hlam, hphi, u3ehi1]
                · linarith only [h1, h2, h879, hc45, hlam, hphi, ht34, u3ehi1]

end R2N4
