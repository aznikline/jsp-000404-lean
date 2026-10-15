import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3258000 in
set_option maxHeartbeats 3258000 in
theorem r1l7_10_12_13_25_L_R_L_R_L_I_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                                  · linarith only [h0, h14, h17, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h14, h16, h17, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h11, h13, h16, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h0, h12, h15, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h11, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h24 | h24
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                                · linarith only [h0, h13, h23, h25, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                                  · linarith only [h0, h13, h23, h27, h8, hc01, hc15, hlam, hphi, ht0b, ht5b]
                                  · rcases h5bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h13, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h25, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      rcases p29_3 (m.d 0 5) (by simp) with h33 | h33
                                      · rcases p29_3 (m.d 1 5) (by simp) with h34 | h34
                                        · linarith only [h2, h34, hlam]
                                        · linarith only [h12, h34, hlam]
                                      · linarith only [h33, h6, hlam]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h13, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h2, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h25, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi3]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h12, h27, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h13, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h5, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h10, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h27, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h25, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h6, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h12, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h24, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h27, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h7, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h4, h7, hc01, hc15, hlam, hphi, ht0b, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h4, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h27, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                              · linarith only [h0, h12, h24, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h11, h23, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                          · linarith only [h11, h12, h61, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h64 | h64
                              · linarith only [h0, h12, h64, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h66 | h66
                                · linarith only [h61, h66, h9, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h68 | h68
                                  · linarith only [h61, h68, h9, hc34, hlam, hphi, ht23, u2ehi3]
                                  · rcases h5bigk with h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [hlam, p70_0]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h0, h11, h12, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi3]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h0, h3, h6, h63, h64, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi3]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h0, h11, h12, h3, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi3]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h0, h11, h12, h3, h6, h68, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi3]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h2, hlam, p70_0]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [hlam, p70_0]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h63, h64, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi3]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h12, hlam, p70_1]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h61, hlam, p70_1]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h5, hlam, p70_1]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h10, hlam, p70_1]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [hlam, p70_0]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h64, hlam, p70_1]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h66, hlam, p70_1]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h6, hlam, p70_0]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p70_1]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h0, h4, h63, h64, h68, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi3]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [hlam, p70_0]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h68, hlam, p70_1]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h7, hlam, p70_0]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h0, h10, h4, h63, h64, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi3]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h0, h4, h63, h64, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi3]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [h0, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p70_1]
                                    · have p70_0 := h70c.1
                                      have p70_1 := h70c.2.1
                                      have p70_2 := h70c.2.2.1
                                      have p70_3 := h70c.2.2.2
                                      linarith only [hlam, p70_0]
                            · linarith only [h11, h12, h63, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h97 | h97
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h99 | h99
                            · linarith only [h0, h11, h3, h97, h99, hc01, hc35, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h101 | h101
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h102 | h102
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h103 | h103
                                  · rcases h5bigk with h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h0, h10, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p104_1, u2ehi4]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p104_1, u2ehi4]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      rcases p104_3 (m.d 0 5) (by simp) with h108 | h108
                                      · rcases p104_3 (m.d 1 5) (by simp) with h109 | h109
                                        · linarith only [h109, h2, hlam]
                                        · linarith only [h109, h97, hlam]
                                      · linarith only [h108, h6, hlam]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      rcases p104_3 (m.d 0 5) (by simp) with h113 | h113
                                      · rcases p104_3 (m.d 1 5) (by simp) with h114 | h114
                                        · linarith only [h114, h2, hlam]
                                        · linarith only [h114, h98, hlam]
                                      · linarith only [h113, h7, hlam]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h2, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h97, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p104_1, u2ehi4]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h11, h97, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h0, h101, h11, h9, h97, h99, hc01, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p104_1, u2ehi4]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h5, hlam, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h10, hlam, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h0, h101, h103, h9, h99, hc01, hc45, hlam, hphi, ht0b, ht5b, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h0, h101, h9, h99, hc01, hc45, hlam, hphi, ht0b, ht5b, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h6, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h97, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h101, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p104_1]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h7, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h98, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h102, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [h103, hlam, p104_0]
                                    · have p104_0 := h104c.1
                                      have p104_1 := h104c.2.1
                                      have p104_2 := h104c.2.2.1
                                      have p104_3 := h104c.2.2.2
                                      linarith only [hlam, p104_0]
                                  · linarith only [h0, h101, h103, h11, h4, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                · linarith only [h101, h102, h11, h97, h98, h99, hc34, hlam, hphi, ht23, u2ehi4]
                              · linarith only [h101, h11, h97, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h11, h97, h98, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h142 | h142
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h143 | h143
                            · linarith only [h11, h143, h8, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h145 | h145
                              · linarith only [h145, h8, h97, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h147 | h147
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                                  · rcases h5bigk with h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c | h149c
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h0, h3, h6, h8, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p149_1, u2ehi2]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h0, h145, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p149_1, u2ehi2]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h0, h3, h6, h8, h97, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p149_1, u2ehi2]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      rcases p149_3 (m.d 0 5) (by simp) with h154 | h154
                                      · rcases p149_3 (m.d 1 5) (by simp) with h155 | h155
                                        · linarith only [h155, h2, hlam]
                                        · linarith only [h142, h155, hlam]
                                      · linarith only [h154, h7, hlam]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h2, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h142, h145, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p149_1, u2ehi2]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h97, hlam, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h5, hlam, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h10, hlam, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h145, hlam, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h0, h147, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h6, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p149_1]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h7, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h142, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h147, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [h148, hlam, p149_0]
                                    · have p149_0 := h149c.1
                                      have p149_1 := h149c.2.1
                                      have p149_2 := h149c.2.2.1
                                      have p149_3 := h149c.2.2.2
                                      linarith only [hlam, p149_0]
                                  · linarith only [h0, h11, h148, h4, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h142, h147, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                            · linarith only [h11, h181, h8, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                              · linarith only [h183, h8, h97, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                                · linarith only [h11, h142, h185, h8, hc24, hlam, hphi, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                                  · linarith only [h11, h142, h187, h8, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h11, h187, h8, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h10, h5, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h8, h9, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                  · linarith only [h192, h8, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
                    · linarith only [h0, h194, h3, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h196 | h196
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h198 | h198
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h199 | h199
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h200 | h200
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h201 | h201
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h202 | h202
                                  · rcases h5bigk with h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h0, h194, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p203_1, u2ehi1]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p203_1, u2ehi4]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      rcases p203_3 (m.d 0 5) (by simp) with h207 | h207
                                      · rcases p203_3 (m.d 1 5) (by simp) with h208 | h208
                                        · linarith only [h2, h208, hlam]
                                        · linarith only [h197, h208, hlam]
                                      · linarith only [h207, h6, hlam]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      rcases p203_3 (m.d 0 5) (by simp) with h212 | h212
                                      · rcases p203_3 (m.d 1 5) (by simp) with h213 | h213
                                        · linarith only [h2, h213, hlam]
                                        · linarith only [h198, h213, hlam]
                                      · linarith only [h212, h7, hlam]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h2, hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h194, hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p203_1]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h1, h196, h198, hc01, hc45, hlam, hphi, ht0b, ht5b, p203_1]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h5, hlam, p203_1]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p203_1]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h0, h200, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p203_1]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h0, h199, h201, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p203_1]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h6, hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h197, hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h200, hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p203_1]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h7, hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h198, hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h201, hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [h202, hlam, p203_0]
                                    · have p203_0 := h203c.1
                                      have p203_1 := h203c.2.1
                                      have p203_2 := h203c.2.2.1
                                      have p203_3 := h203c.2.2.2
                                      linarith only [hlam, p203_0]
                                  · rcases h5bigk with h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c | h237c
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h0, h194, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p237_1, u2ehi1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p237_1, u2ehi4]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      rcases p237_3 (m.d 0 5) (by simp) with h241 | h241
                                      · rcases p237_3 (m.d 1 5) (by simp) with h242 | h242
                                        · linarith only [h2, h242, hlam]
                                        · linarith only [h197, h242, hlam]
                                      · linarith only [h241, h6, hlam]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h0, h202, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p237_1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h2, hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h194, hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p237_1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p237_1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h5, hlam, p237_1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h0, h5, hc01, hc15, hlam, hphi, ht0b, ht5b, p237_1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h0, h200, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p237_1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h0, h199, h201, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p237_1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h6, hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h197, hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h200, hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h202, hlam, p237_1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h7, hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h198, hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h201, hlam, p237_0]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [h0, h4, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p237_1]
                                    · have p237_0 := h237c.1
                                      have p237_1 := h237c.2.1
                                      have p237_2 := h237c.2.2.1
                                      have p237_3 := h237c.2.2.2
                                      linarith only [hlam, p237_0]
                                · linarith only [h0, h196, h198, h201, h3, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h0, h200, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h199, h8, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h271 | h271
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h272 | h272
                                · linarith only [h0, h192, h198, h270, h272, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h192, h272, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h1, h197, h271, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h270, h8, hc34, hlam, hphi, ht23, u2ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                          · linarith only [h196, h197, h277, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h280 | h280
                              · linarith only [h0, h196, h197, h280, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h0, h280, h3, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h279, h8, hc34, hlam, hphi, ht23, u2ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h284 | h284
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h285 | h285
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h286 | h286
                            · linarith only [h0, h196, h284, h286, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h286, h8, hc34, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h196, h284, h285, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                            · linarith only [h0, h196, h291, h3, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h291, h8, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                            · linarith only [h196, h294, h8, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h294, h8, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h297 | h297
                · rcases m.htr 1 2 4 (by decide) (by decide) with h298 | h298
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h299 | h299
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h300 | h300
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h301 | h301
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h302 | h302
                          · linarith only [h300, h302, h7, hc13, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h304 | h304
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h305 | h305
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h306 | h306
                                · linarith only [h298, h306, h7, hc14, hlam, hphi, ht01, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h308 | h308
                                  · linarith only [h0, h297, h304, h308, h7, hc01, hlam, hphi, u0ehi3]
                                  · rcases h5bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [hlam, p310_0]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h299, h306, h7, hc24, hc45, hlam, hphi, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h306, h7, hc45, hlam, hphi, ht23, ht34, p310_1, u2ehi3]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h308, h7, hc34, hc45, hlam, hphi, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h7, hlam, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h2, hlam, p310_0]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [hlam, p310_0]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h306, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p310_1, u2ehi3]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h0, h297, h301, h308, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h302, hlam, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h5, hlam, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h299, hlam, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [hlam, p310_0]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h0, h308, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h306, hlam, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h6, hlam, p310_0]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h301, hlam, p310_0]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h305, hlam, p310_0]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [hlam, p310_0]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h308, hlam, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p310_1, u0ehi4]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h299, hc45, hlam, hphi, ht23, ht34, p310_1, u2ehi4]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht23, ht34, p310_1, u2ehi4]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [h308, hc34, hc45, hlam, hphi, p310_1]
                                    · have p310_0 := h310c.1
                                      have p310_1 := h310c.2.1
                                      have p310_2 := h310c.2.2.1
                                      have p310_3 := h310c.2.2.2
                                      linarith only [hlam, p310_0]
                              · linarith only [h0, h297, h301, h305, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h297, h300, h304, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h338 | h338
                          · linarith only [h338, h7, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h340 | h340
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h341 | h341
                              · linarith only [h0, h297, h301, h341, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h343 | h343
                                · linarith only [h298, h300, h301, h343, h6, h7, hc05, hlam, hphi, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                                  · linarith only [h0, h297, h3, h301, h340, h345, h6, h7, hc01, hc05, hlam, hphi, ht0b, ht5b]
                                  · rcases h5bigk with h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c | h347c
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [hlam, p347_0]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h297, h301, h340, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h0, h340, h341, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h0, h3, h301, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h7, hlam, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h2, hlam, p347_0]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [hlam, p347_0]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h341, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p347_1, u2ehi2]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h301, hlam, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h338, hlam, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h5, hlam, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h299, hlam, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [hlam, p347_0]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h341, hlam, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h343, hlam, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h6, hlam, p347_0]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h0, h3, h6, hc01, hc15, hlam, hphi, ht0b, ht5b, p347_1]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h0, h3, h340, h341, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p347_1, u2ehi3]
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
                                      linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p347_1, u0ehi4]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h298, h300, h301, hc45, hlam, hphi, ht23, ht34, p347_1, u2ehi3]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h340, h341, hc45, hlam, hphi, ht23, ht34, p347_1, u2ehi3]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [h298, h300, h301, hc45, hlam, hphi, ht23, ht34, p347_1, u2ehi3]
                                    · have p347_0 := h347c.1
                                      have p347_1 := h347c.2.1
                                      have p347_2 := h347c.2.2.1
                                      have p347_3 := h347c.2.2.2
                                      linarith only [hlam, p347_0]
                            · linarith only [h0, h3, h300, h301, h340, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                          · linarith only [h375, h7, hc14, hlam, hphi, ht01, u0ehi3]
                          · linarith only [h300, h374, h375, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h378 | h378
                          · linarith only [h378, h7, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h380 | h380
                            · linarith only [h0, h297, h300, h380, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h382 | h382
                              · linarith only [h297, h374, h382, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h384 | h384
                                · linarith only [h384, h4, h7, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h386 | h386
                                  · linarith only [h386, h7, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                                  · linarith only [h297, h300, h386, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h297, h299, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h297, h298, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                  · linarith only [h297, h391, hc23, hlam, hphi, u2ehi3]
                  · linarith only [h391, h4, h7, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h394 | h394
              · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
                · rcases m.htr 1 2 4 (by decide) (by decide) with h396 | h396
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h397 | h397
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h398 | h398
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h399 | h399
                        · linarith only [h1, h399, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h401 | h401
                          · linarith only [h398, h399, h401, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h403 | h403
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h404 | h404
                              · linarith only [h1, h395, h404, h6, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h406 | h406
                                · linarith only [h396, h401, h406, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h408 | h408
                                  · linarith only [h1, h395, h396, h401, h403, h408, h6, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                  · linarith only [h0, h394, h4, h408, h6, hc01, hlam, hphi, u0ehi2]
                            · linarith only [h1, h398, h403, h6, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h412 | h412
                        · linarith only [h1, h412, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h414 | h414
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                            · linarith only [h3, h398, h415, h6, hc13, hc35, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h417 | h417
                              · linarith only [h0, h396, h415, h417, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h419 | h419
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h420 | h420
                                  · rcases h5bigk with h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c | h421c
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h395, h412, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p421_1, u2ehi2]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p421_1, u2ehi4]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h6, hlam, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      rcases p421_3 (m.d 0 5) (by simp) with h426 | h426
                                      · rcases p421_3 (m.d 1 5) (by simp) with h427 | h427
                                        · linarith only [h2, h427, hlam]
                                        · linarith only [h414, h427, hlam]
                                      · linarith only [h394, h426, hlam]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h2, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h417, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p421_1, u2ehi2]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h412, hlam, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, h396, h414, hc01, hc45, hlam, hphi, ht0b, ht5b, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h5, hlam, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h397, hlam, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h417, hlam, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p421_1]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h420, hc34, hlam, hphi, ht01, ht12, ht23, p421_1, u0ehi4]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h397, h420, hc34, hlam, hphi, ht23, p421_1, u2ehi4]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h420, hc34, hlam, hphi, ht23, p421_1, u2ehi4]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      rcases p421_3 (m.d 0 5) (by simp) with h445 | h445
                                      · linarith only [h445, h6, hlam]
                                      · linarith only [h394, h445, hlam]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h394, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h414, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h419, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [h420, hlam, p421_0]
                                    · have p421_0 := h421c.1
                                      have p421_1 := h421c.2.1
                                      have p421_2 := h421c.2.2.1
                                      have p421_3 := h421c.2.2.2
                                      linarith only [hlam, p421_0]
                                  · linarith only [h395, h398, h420, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h0, h396, h414, h419, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h455 | h455
                            · linarith only [h395, h398, h455, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h457 | h457
                              · linarith only [h395, h457, h6, hc13, hlam, hphi, ht01, u0ehi2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h459 | h459
                                · linarith only [h396, h414, h459, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h461 | h461
                                  · linarith only [h395, h398, h414, h461, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h0, h394, h395, h398, h4, h461, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h395, h397, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h395, h396, hc24, hlam, hphi, u2ehi2]
                · linarith only [h3, h395, h6, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h467 | h467
                · rcases m.htr 1 2 4 (by decide) (by decide) with h468 | h468
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h469 | h469
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h470 | h470
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h471 | h471
                        · linarith only [h1, h471, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h473 | h473
                          · linarith only [h1, h394, h470, h473, h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h475 | h475
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h476 | h476
                              · linarith only [h0, h467, h476, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h478 | h478
                                · linarith only [h394, h468, h470, h478, hc13, hlam, hphi, ht01, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h480 | h480
                                  · linarith only [h0, h394, h469, h475, h476, h480, hc01, hlam, hphi, u0ehi3]
                                  · rcases h5bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h469, h476, h480, h6, hc23, hc45, hlam, hphi, ht34, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h475, h476, h480, h6, hc45, hlam, hphi, ht23, ht34, p482_1, u2ehi3]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h6, hlam, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h394, hlam, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h2, hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h475, h476, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p482_1, u2ehi3]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h471, hlam, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h473, hlam, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h5, hlam, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h469, hlam, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h476, hlam, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h478, hlam, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h480, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p482_1, u0ehi4]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h469, h475, h476, h480, hc45, hlam, hphi, ht23, ht34, p482_1, u2ehi3]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h475, h476, h480, hc45, hlam, hphi, ht23, ht34, p482_1, u2ehi3]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h480, hlam, p482_1]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h1, h467, h475, h6, hc45, hlam, hphi, ht23, ht34, p482_1, u2ehi3]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h469, h475, h476, hc45, hlam, hphi, ht23, ht34, p482_1, u2ehi3]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h475, h476, hc45, hlam, hphi, ht23, ht34, p482_1, u2ehi3]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [h1, h467, h475, h6, hc45, hlam, hphi, ht23, ht34, p482_1, u2ehi3]
                                    · have p482_0 := h482c.1
                                      have p482_1 := h482c.2.1
                                      have p482_2 := h482c.2.2.1
                                      have p482_3 := h482c.2.2.2
                                      linarith only [hlam, p482_0]
                            · linarith only [h1, h470, h475, h6, hc35, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h509 | h509
                        · linarith only [h1, h509, h6, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h511 | h511
                          · linarith only [h394, h511, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h513 | h513
                            · linarith only [h3, h470, h513, h6, hc13, hc35, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h515 | h515
                              · linarith only [h467, h470, h515, h6, hc03, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h517 | h517
                                · linarith only [h394, h468, h517, hc12, hlam, hphi, ht01, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h519 | h519
                                  · linarith only [h394, h519, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                                  · linarith only [h467, h470, h519, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h467, h469, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h467, h468, hc24, hlam, hphi, u2ehi2]
                · linarith only [h3, h467, h6, hc35, hlam, hphi, ht23, u2ehi1]
          · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
        · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h527 | h527
        · linarith only [h3, h527, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h529 | h529
          · linarith only [h3, h529, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h531 | h531
            · rcases m.htr 0 4 5 (by decide) (by decide) with h532 | h532
              · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                · linarith only [h3, h533, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h535 | h535
                  · linarith only [h527, h535, hc12, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h537 | h537
                    · linarith only [h0, h529, h537, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h539 | h539
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h540 | h540
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h541 | h541
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h542 | h542
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h543 | h543
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h544 | h544
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h545 | h545
                                  · rcases h5bigk with h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c | h546c
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h532, h537, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p546_1, u2ehi1]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h529, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      rcases p546_3 (m.d 0 5) (by simp) with h550 | h550
                                      · rcases p546_3 (m.d 1 5) (by simp) with h551 | h551
                                        · linarith only [h2, h551, hlam]
                                        · linarith only [h540, h551, hlam]
                                      · linarith only [h531, h550, hlam]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      rcases p546_3 (m.d 0 5) (by simp) with h555 | h555
                                      · rcases p546_3 (m.d 1 5) (by simp) with h556 | h556
                                        · linarith only [h2, h556, hlam]
                                        · linarith only [h541, h556, hlam]
                                      · linarith only [h532, h555, hlam]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h2, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h537, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p546_1]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h1, h539, h541, hc01, hc45, hlam, hphi, ht0b, ht5b, p546_1]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [hc25, hlam, hphi, ht01, ht12, p546_1, u0ehi4]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h537, hc25, hlam, hphi, p546_1, u2ehi1]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      rcases p546_3 (m.d 0 5) (by simp) with h568 | h568
                                      · linarith only [h529, h568, hlam]
                                      · linarith only [h531, h568, hlam]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      rcases p546_3 (m.d 0 5) (by simp) with h571 | h571
                                      · linarith only [h529, h571, hlam]
                                      · linarith only [h532, h571, hlam]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h531, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h540, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h543, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h531, hc03, hc45, hlam, hphi, ht0b, ht5b, p546_1]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h532, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h541, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h544, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [h545, hlam, p546_0]
                                    · have p546_0 := h546c.1
                                      have p546_1 := h546c.2.1
                                      have p546_2 := h546c.2.2.1
                                      have p546_3 := h546c.2.2.2
                                      linarith only [hlam, p546_0]
                                  · rcases h5bigk with h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h537, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p584_1, u2ehi1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h529, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      rcases p584_3 (m.d 0 5) (by simp) with h588 | h588
                                      · rcases p584_3 (m.d 1 5) (by simp) with h589 | h589
                                        · linarith only [h2, h589, hlam]
                                        · linarith only [h540, h589, hlam]
                                      · linarith only [h531, h588, hlam]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h529, h542, h544, h545, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h2, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h537, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h2, hc01, hc35, hlam, hphi, ht0b, ht5b, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h1, h539, h541, h545, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h542, h544, hc23, hlam, hphi, ht01, ht12, p584_1, u0ehi4]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h537, h542, h544, hc23, hlam, hphi, p584_1, u2ehi1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      rcases p584_3 (m.d 0 5) (by simp) with h602 | h602
                                      · linarith only [h529, h602, hlam]
                                      · linarith only [h531, h602, hlam]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h542, h544, h545, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h531, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h540, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h543, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h545, hlam, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h532, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h541, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h544, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h545, hc34, hc45, hlam, hphi, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                · linarith only [h1, h527, h539, h541, h544, hc01, hlam, hphi, u0ehi3]
                              · linarith only [h3, h543, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h3, h542, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h527, h532, h535, h541, hc24, hlam, hphi, u2ehi1]
                        · linarith only [h3, h531, h533, h540, hc23, hlam, hphi, u2ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h621 | h621
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h622 | h622
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h623 | h623
                            · linarith only [h533, h539, h623, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h3, h623, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h527, h532, h537, h539, h621, h622, hc24, hlam, hphi, u2ehi1]
                        · linarith only [h3, h531, h533, h621, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
                · linarith only [h0, h3, h628, hc01, hlam, hphi, u0ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h630 | h630
                  · linarith only [h0, h3, h630, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h632 | h632
                    · linarith only [h0, h529, h632, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h634 | h634
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h635 | h635
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h636 | h636
                          · linarith only [h527, h532, h634, h636, hc13, hlam, hphi, ht01, u0ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h638 | h638
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h639 | h639
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h640 | h640
                                · linarith only [h527, h532, h640, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                                · linarith only [h527, h640, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                              · linarith only [h2, h3, h635, h639, hc05, hlam, hphi, u0ehi1]
                            · linarith only [h3, h638, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                        · linarith only [h3, h531, h628, h635, hc23, hlam, hphi, u2ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h646 | h646
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h647 | h647
                          · linarith only [h527, h532, h647, hc14, hlam, hphi, ht01, u0ehi1]
                          · linarith only [h634, h646, h647, hlam]
                        · linarith only [h3, h531, h628, h646, hc23, hlam, hphi, u2ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h651 | h651
              · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
                · linarith only [h0, h3, h652, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h654 | h654
                  · linarith only [h0, h3, h531, h654, hc35, hlam, hphi, ht23, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h656 | h656
                    · linarith only [h0, h3, h531, h656, hc35, hlam, hphi, ht23, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h658 | h658
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h659 | h659
                        · linarith only [h1, h531, h659, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h661 | h661
                          · linarith only [h658, h659, h661, hlam]
                          · linarith only [h527, h651, h654, h661, hc24, hlam, hphi, u2ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h664 | h664
                        · linarith only [h3, h531, h664, hc13, hlam, hphi, ht01, u0ehi1]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h667 | h667
                            · linarith only [h652, h658, h667, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h3, h667, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h527, h651, h654, h666, hc24, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h671 | h671
                · linarith only [h3, h671, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h673 | h673
                  · linarith only [h0, h3, h673, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h675 | h675
                    · linarith only [h0, h529, h675, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h677 | h677
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h678 | h678
                        · linarith only [h1, h531, h678, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h680 | h680
                          · linarith only [h527, h651, h677, h678, h680, hc15, hlam, hphi, ht01, u0ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h682 | h682
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h683 | h683
                              · linarith only [h531, h683, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                              · linarith only [h3, h683, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                            · linarith only [h1, h3, h677, h682, hc03, hlam, hphi, u0ehi1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h687 | h687
                        · linarith only [h1, h531, h687, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h689 | h689
                          · linarith only [h527, h651, h689, hc14, hlam, hphi, ht01, u0ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h691 | h691
                            · linarith only [h671, h677, h691, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h3, h691, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h694 | h694
      · rcases m.htr 0 2 4 (by decide) (by decide) with h695 | h695
        · rcases m.htr 0 2 5 (by decide) (by decide) with h696 | h696
          · linarith only [h0, h2, h696, hlam]
          · linarith only [h694, h696, hc25, hlam, hphi, u2ehi2]
        · linarith only [h694, h695, hc24, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h700 | h700
        · linarith only [h694, h700, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h702 | h702
          · linarith only [h694, h702, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h704 | h704
            · linarith only [h1, h2, h704, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h706 | h706
              · rcases m.htr 1 2 3 (by decide) (by decide) with h707 | h707
                · linarith only [h0, h2, h707, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h709 | h709
                  · linarith only [h1, h2, h700, h706, h707, h709, hc15, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h711 | h711
                    · linarith only [h1, h2, h702, h707, h711, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1, h2, h707, h711, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h714 | h714
                · linarith only [h694, h714, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h716 | h716
                  · linarith only [h1, h2, h700, h714, h716, hc15, hlam, hphi, ht01, u0ehi1]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h718 | h718
                    · linarith only [h1, h2, h714, h718, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h1, h2, h714, h718, hc25, hlam, hphi, u2ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h721 | h721
    · rcases m.htr 0 2 3 (by decide) (by decide) with h722 | h722
      · linarith only [h0, h1, h722, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h724 | h724
        · linarith only [h722, h724, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h726 | h726
          · linarith only [h722, h726, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h728 | h728
            · rcases m.htr 0 4 5 (by decide) (by decide) with h729 | h729
              · rcases m.htr 1 2 3 (by decide) (by decide) with h730 | h730
                · linarith only [h722, h730, hc12, hlam, hphi, ht01, u0ehi1]
                · linarith only [h0, h1, h730, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
                · linarith only [h0, h1, h733, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h0, h1, h733, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h728, hc35, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h737 | h737
      · linarith only [h0, h1, h737, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h739 | h739
        · linarith only [h737, h739, hc23, hlam, hphi, u2ehi3]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h741 | h741
          · linarith only [h737, h741, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h743 | h743
            · rcases m.htr 0 4 5 (by decide) (by decide) with h744 | h744
              · rcases m.htr 1 2 3 (by decide) (by decide) with h745 | h745
                · linarith only [h0, h737, h745, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h1, h745, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h748 | h748
                · linarith only [h0, h1, h737, h743, h748, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h0, h1, h748, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h743, hc35, hlam, hphi, ht23, u2ehi1]

end R2N4
