import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
    · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
      · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
          · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h10, h13, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h16, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h10, h16, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h10, h11, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
              · linarith only [h0, h10, h20, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h0, h10, h23, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                    · linarith only [h20, h25, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                        · rcases h4bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h27, h4, h6, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h27, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h20, h28, h4, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            rcases p29_3 (m.d 0 4) (by simp) with h34 | h34
                            · rcases p29_3 (m.d 1 4) (by simp) with h35 | h35
                              · linarith only [h2, h35, hlam]
                              · linarith only [h22, h35, hlam]
                            · linarith only [h34, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h2, hlam, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h25, h27, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p29_1, u3ehi2]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h10, hlam, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h5, hlam, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h9, hlam, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h23, hlam, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h6, hlam, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h7, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h22, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h27, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [h28, hlam, p29_0]
                          · have p29_0 := h29c.1
                            have p29_1 := h29c.2.1
                            have p29_2 := h29c.2.2.1
                            have p29_3 := h29c.2.2.2
                            linarith only [hlam, p29_0]
                        · linarith only [h0, h10, h28, h4, h6, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h2, h22, h23, h27, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
                  · linarith only [h20, h61, h8, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h63 | h63
                    · linarith only [h0, h20, h4, h63, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h22, h65, h9, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                        · linarith only [h0, h10, h22, h4, h6, h67, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h10, h4, h6, h67, h7, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h0, h5, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h71 | h71
          · rcases m.htr 1 3 4 (by decide) (by decide) with h72 | h72
            · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
              · rcases m.htr 1 4 5 (by decide) (by decide) with h74 | h74
                · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                  · linarith only [h0, h4, h71, h75, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h71, h72, h75, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                  · linarith only [h0, h4, h71, h78, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h4, h6, h71, h78, h8, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h72, h73, hc35, hlam, hphi, u3ehi3]
            · linarith only [h71, h72, h8, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
            · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
              · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h87 | h87
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h88 | h88
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                        · rcases h4bigk with h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, h4, h6, h83, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p90_1, u3ehi4]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, h4, h6, h71, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, h4, h6, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p90_1, u3ehi4]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            rcases p90_3 (m.d 0 4) (by simp) with h95 | h95
                            · rcases p90_3 (m.d 1 4) (by simp) with h96 | h96
                              · linarith only [h2, h96, hlam]
                              · linarith only [h85, h96, hlam]
                            · linarith only [h95, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h2, hlam, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h71, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h89, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p90_1, u3ehi4]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, h4, h8, h83, hc01, hc45, hlam, hphi, ht0b, ht5b, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h5, hlam, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, h4, h86, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p90_1, u3ehi4]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, h4, h86, hc01, hc45, hlam, hphi, ht0b, ht5b, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h6, hlam, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h83, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h86, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h2, h83, hc01, hc45, hlam, hphi, ht0b, ht5b, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h7, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h85, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h88, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h89, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                        · linarith only [h0, h4, h71, h85, h86, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h71, h85, h88, hlam]
                    · linarith only [h8, h83, h87, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h8, h83, h86, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                      · linarith only [h0, h124, h126, h4, h83, h85, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h128 | h128
                        · linarith only [h126, h128, h71, h83, hlam]
                        · rcases h4bigk with h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c | h130c
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h6, h83, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p130_1, u3ehi3]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h0, h4, h6, h71, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p130_1, u3ehi3]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p130_1, u3ehi3]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h0, h126, h4, h6, h71, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p130_1, u3ehi3]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h2, hlam, p130_1]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h71, hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p130_1, u3ehi3]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h85, hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h5, hlam, p130_1]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h126, hc14, hc45, hlam, hphi, p130_1]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h0, h126, h4, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p130_1, u3ehi3]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h126, hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h6, hlam, p130_1]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h83, hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h124, hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h128, hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h7, hlam, p130_0]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h0, h4, h6, h7, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p130_1, u3ehi3]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h0, h4, h6, h7, h71, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p130_1]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [h0, h4, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p130_1, u3ehi3]
                          · have p130_0 := h130c.1
                            have p130_1 := h130c.2.1
                            have p130_2 := h130c.2.2.1
                            have p130_3 := h130c.2.2.2
                            linarith only [hlam, p130_0]
                    · linarith only [h1, h125, h84, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h124, h8, h84, hc34, hlam, hphi, u3ehi4]
              · linarith only [h83, h84, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h159 | h159
              · linarith only [h0, h159, h4, h6, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h161 | h161
                · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                  · linarith only [h0, h162, h4, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h164 | h164
                    · linarith only [h162, h164, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                        · rcases h4bigk with h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c | h168c
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h161, hc04, hc45, hlam, hphi, ht0b, ht5b, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h0, h161, h5, h71, hc01, hc45, hlam, hphi, ht0b, ht5b, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h0, h164, h167, h4, h6, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            rcases p168_3 (m.d 0 4) (by simp) with h173 | h173
                            · rcases p168_3 (m.d 1 4) (by simp) with h174 | h174
                              · linarith only [h174, h2, hlam]
                              · linarith only [h161, h174, hlam]
                            · linarith only [h173, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h2, hlam, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h71, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h83, hlam, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h5, hlam, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h162, hlam, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h0, h162, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h6, hlam, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h0, h159, h161, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p168_1, u3ehi1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h0, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p168_1]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h7, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h161, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h166, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [h167, hlam, p168_0]
                          · have p168_0 := h168c.1
                            have p168_1 := h168c.2.1
                            have p168_2 := h168c.2.2.1
                            have p168_3 := h168c.2.2.2
                            linarith only [hlam, p168_0]
                        · linarith only [h0, h167, h4, h6, h7, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h161, h166, h71, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                  · linarith only [h0, h200, h4, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                    · linarith only [h200, h202, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h0, h161, h204, h5, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                        · linarith only [h0, h200, h204, h206, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h0, h206, h4, h6, h7, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h209 | h209
        · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
          · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
            · rcases m.htr 1 3 5 (by decide) (by decide) with h212 | h212
              · rcases m.htr 1 4 5 (by decide) (by decide) with h213 | h213
                · linarith only [h2, h213, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h215 | h215
                  · linarith only [h0, h209, h215, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h2, h211, h215, h7, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h211, h212, hc35, hlam, hphi, u3ehi3]
            · linarith only [h211, h6, h7, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h209, h210, h5, h7, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
          · rcases m.htr 1 3 4 (by decide) (by decide) with h222 | h222
            · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
              · rcases m.htr 1 4 5 (by decide) (by decide) with h224 | h224
                · linarith only [h2, h224, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h226 | h226
                  · linarith only [h0, h209, h221, h226, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h209, h221, h222, h226, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h222, h223, hc35, hlam, hphi, u3ehi3]
            · linarith only [h222, h6, h7, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h231 | h231
            · rcases m.htr 1 3 5 (by decide) (by decide) with h232 | h232
              · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
                · linarith only [h2, h233, h7, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h235 | h235
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h237 | h237
                      · linarith only [h237, h5, h7, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                        · linarith only [h221, h231, h239, h5, h7, hlam]
                        · rcases h4bigk with h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h231, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p241_1, u3ehi3]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h221, h231, h7, hc45, hlam, hphi, ht34, p241_1, u3ehi3]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h7, hc45, hlam, hphi, ht34, p241_1, u3ehi3]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h7, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h2, hlam, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h221, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p241_1, u3ehi3]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h233, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h5, hlam, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h5, h7, hc45, hlam, hphi, ht34, p241_1, u3ehi3]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h237, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h6, hlam, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h231, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h235, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h239, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hc04, hc45, hlam, hphi, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h231, hc45, hlam, hphi, ht34, p241_1, u3ehi3]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h221, hc12, hc45, hlam, hphi, ht23, ht34, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hc45, hlam, hphi, ht34, p241_1, u3ehi3]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                    · linarith only [h1, h232, h236, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h209, h232, h235, hc34, hlam, hphi, u3ehi4]
              · linarith only [h231, h232, hc35, hlam, hphi, u3ehi3]
            · linarith only [h231, h6, h7, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h271 | h271
      · rcases m.htr 1 2 3 (by decide) (by decide) with h272 | h272
        · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
          · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
            · linarith only [h1, h274, h6, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
              · linarith only [h1, h276, h6, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                  · linarith only [h0, h279, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h281 | h281
                    · linarith only [h272, h276, h281, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h283 | h283
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
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
                            linarith only [h272, h276, h278, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p285_1, u3ehi2]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h281, h283, h6, hc34, hlam, hphi, p285_1, u3ehi2]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h6, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            rcases p285_3 (m.d 0 4) (by simp) with h290 | h290
                            · rcases p285_3 (m.d 1 4) (by simp) with h291 | h291
                              · linarith only [h2, h291, hlam]
                              · linarith only [h278, h291, hlam]
                            · linarith only [h290, hlam, p285_0]
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
                            linarith only [h281, h283, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p285_1, u3ehi2]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h274, hlam, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h0, h273, hc01, hc45, hlam, hphi, ht0b, ht5b, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h5, hlam, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h273, hlam, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h279, hlam, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p285_1]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h271, h272, h276, h3, hc34, hlam, hphi, p285_1, u3ehi2]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h272, h274, hc34, hlam, hphi, p285_1, u3ehi2]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h279, hc34, hlam, hphi, p285_1, u3ehi2]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            rcases p285_3 (m.d 0 4) (by simp) with h309 | h309
                            · linarith only [h309, h6, hlam]
                            · linarith only [h271, h309, hlam]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h271, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h278, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h283, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [h284, hlam, p285_0]
                          · have p285_0 := h285c.1
                            have p285_1 := h285c.2.1
                            have p285_2 := h285c.2.2.1
                            have p285_3 := h285c.2.2.2
                            linarith only [hlam, p285_0]
                        · linarith only [h1, h272, h284, h6, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h2, h278, h279, h283, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h271, h272, h274, h278, h6, hc34, hlam, hphi, u3ehi2]
          · linarith only [h0, h272, h273, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h321 | h321
          · rcases m.htr 1 3 4 (by decide) (by decide) with h322 | h322
            · linarith only [h272, h321, h322, h4, h6, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h272, h321, h322, h4, h6, hc34, hlam, hphi, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h325 | h325
            · linarith only [h1, h325, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h327 | h327
              · linarith only [h1, h327, h6, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h329 | h329
                · rcases m.htr 2 3 4 (by decide) (by decide) with h330 | h330
                  · linarith only [h330, h4, h6, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h332 | h332
                    · linarith only [h327, h332, h4, h6, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h334 | h334
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h335 | h335
                        · rcases h4bigk with h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h327, h329, h6, hc34, hlam, hphi, p336_1, u3ehi1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h332, h334, h6, hc34, hlam, hphi, p336_1, u3ehi2]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h6, hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            rcases p336_3 (m.d 0 4) (by simp) with h341 | h341
                            · rcases p336_3 (m.d 1 4) (by simp) with h342 | h342
                              · linarith only [h2, h342, hlam]
                              · linarith only [h329, h342, hlam]
                            · linarith only [h341, hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h2, hlam, p336_1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h321, hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h325, hlam, p336_1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p336_1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h5, hlam, p336_1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p336_1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h330, hlam, p336_1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p336_1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h2, h327, h329, hc34, hlam, hphi, p336_1, u3ehi1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h327, h329, hc34, hlam, hphi, p336_1, u3ehi1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h321, hc12, hc34, hlam, hphi, ht23, p336_1]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            rcases p336_3 (m.d 0 4) (by simp) with h360 | h360
                            · linarith only [h360, h6, hlam]
                            · linarith only [h271, h360, hlam]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h271, hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h329, hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h334, hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [h335, hlam, p336_0]
                          · have p336_0 := h336c.1
                            have p336_1 := h336c.2.1
                            have p336_2 := h336c.2.2.1
                            have p336_3 := h336c.2.2.2
                            linarith only [hlam, p336_0]
                        · linarith only [h335, h6, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h321, h329, h334, hlam]
                · linarith only [h271, h325, h329, h6, hc34, hlam, hphi, u3ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
        · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
          · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
            · linarith only [h1, h373, h6, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h375 | h375
              · linarith only [h1, h271, h375, h6, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h377 | h377
                · linarith only [h2, h271, h377, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h379 | h379
                  · linarith only [h371, h375, h379, hc35, hlam, hphi, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h381 | h381
                    · linarith only [h0, h372, h375, h379, h381, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
                      · linarith only [h1, h2, h271, h371, h372, h383, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h385 | h385
                        · linarith only [h271, h379, h385, h5, hc34, hlam, hphi, u3ehi2]
                        · linarith only [h1, h371, h385, h6, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h371, h372, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h389 | h389
          · linarith only [h271, h371, h389, h4, h6, hc24, hc45, hlam, hphi]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
            · linarith only [h371, h391, h4, h6, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h393 | h393
              · linarith only [h271, h371, h393, h4, h6, hc45, hlam, hphi, ht34, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                · linarith only [h271, h371, h389, h395, h4, h6, hc12, hc24, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
                  · linarith only [h397, h4, h6, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h399 | h399
                    · linarith only [h393, h399, h4, h6, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h401 | h401
                      · linarith only [h271, h401, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h403 | h403
                        · linarith only [h271, h403, h6, hc34, hlam, hphi, u3ehi0]
                        · linarith only [h371, h4, h403, h6, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h406 | h406
    · linarith only [h4, h406, h5, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
      · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
        · rcases m.htr 1 2 4 (by decide) (by decide) with h410 | h410
          · linarith only [h0, h410, h5, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h412 | h412
            · linarith only [h1, h406, h412, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h414 | h414
              · linarith only [h1, h406, h414, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h416 | h416
                · rcases m.htr 2 3 4 (by decide) (by decide) with h417 | h417
                  · linarith only [h4, h406, h417, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h4, h417, h5, hc34, hlam, hphi, u3ehi2]
                · linarith only [h408, h409, h410, h416, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · linarith only [h4, h409, h5, hc12, hc24, hlam, hphi]
      · linarith only [h4, h408, h5, hc45, hlam, hphi, ht34, u3ehi2]

end R2N4
