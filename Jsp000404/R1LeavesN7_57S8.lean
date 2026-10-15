import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3900000 in
set_option maxHeartbeats 3900000 in
theorem r1l7_20_12_14_H_I_L_R_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2ehi := hb2.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
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
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                                  · linarith only [h0, h10, h15, h17, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                  · linarith only [h0, h10, h15, h16, h17, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h10, h13, h14, h16, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h0, h10, h13, h15, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h10, h14, h22, h23, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                                  · linarith only [h0, h10, h11, h14, h22, h25, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · rcases h0bigk with h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c | h27c
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h11, h2, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h11, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi4]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h22, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h11, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi4]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h1, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h4, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h11, h2, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi3]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi4]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h2, hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h5, hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h7, hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h6, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p27_1, u2ehi4]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h3, hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h6, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h8, hlam, p27_0]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [h9, hlam, p27_1]
                                    · have p27_0 := h27c.1
                                      have p27_1 := h27c.2.1
                                      have p27_2 := h27c.2.2.1
                                      have p27_3 := h27c.2.2.2
                                      linarith only [hlam, p27_0]
                              · linarith only [h0, h10, h13, h22, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h54 | h54
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                              · linarith only [h0, h10, h13, h54, h55, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h58 | h58
                                  · rcases h0bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p59_1, u2ehi0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h13, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h5, h55, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p59_1, u2ehi2]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h12, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p59_1, u2ehi4]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h0, hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h13, h7, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p59_1]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h0, h5, h55, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p59_1, u2ehi2]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h0, h12, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p59_1, u2ehi4]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h1, hlam, p59_1]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h4, hlam, p59_1]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h5, h55, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p59_1, u2ehi2]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h0, h12, h3, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p59_1, u2ehi4]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h2, hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h5, hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h7, hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h12, h3, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p59_1, u2ehi4]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h3, hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h6, hlam, p59_1]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h8, hlam, p59_0]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [h9, hlam, p59_1]
                                    · have p59_0 := h59c.1
                                      have p59_1 := h59c.2.1
                                      have p59_2 := h59c.2.2.1
                                      have p59_3 := h59c.2.2.2
                                      linarith only [hlam, p59_0]
                                  · linarith only [h10, h13, h58, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h2, h54, h55, h57, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                              · linarith only [h10, h13, h87, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h89 | h89
                                · linarith only [h10, h13, h54, h89, hc24, hlam, hphi, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                                  · linarith only [h10, h13, h54, h91, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h10, h13, h91, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h10, h12, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h96 | h96
                      · linarith only [h10, h96, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h0, h10, h4, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h100 | h100
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h104 | h104
                                  · rcases h0bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h1, h100, h104, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h101, h2, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h3, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h1, h100, h104, hc02, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h101, h2, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h3, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h1, hlam, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h4, hlam, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h103, h5, h98, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h4, h6, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h2, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h5, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h7, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h6, h98, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h3, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h6, hlam, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h8, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h9, hlam, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                  · rcases h0bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h1, h100, h101, h104, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h101, h104, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h6, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h0, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h1, h100, h101, h104, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h0, h101, h104, h2, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h0, h6, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h1, hlam, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h4, hlam, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h101, h104, h5, h96, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h0, h4, h6, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h2, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h5, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h7, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h6, h98, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h3, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h6, hlam, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h8, hlam, p131_0]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [h9, hlam, p131_1]
                                    · have p131_0 := h131c.1
                                      have p131_1 := h131c.2.1
                                      have p131_2 := h131c.2.2.1
                                      have p131_3 := h131c.2.2.2
                                      linarith only [hlam, p131_0]
                                · linarith only [h100, h101, h103, h96, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h0, h10, h102, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                                · linarith only [h0, h101, h159, h160, h4, h96, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h160, h96, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h0, h10, h159, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                              · linarith only [h0, h10, h100, h165, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h10, h165, hc34, hlam, hphi, ht23, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                              · linarith only [h10, h100, h168, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h10, h168, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h173 | h173
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h174 | h174
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h175 | h175
                            · linarith only [h175, h2, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                                · linarith only [h0, h171, h177, h178, h2, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h180 | h180
                                  · linarith only [h0, h171, h177, h180, h9, hc01, hc05, hlam, hphi, ht0b, ht5b]
                                  · rcases h0bigk with h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c | h182c
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p182_1, u2ehi0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h1, h171, h177, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p182_1]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h172, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p182_1, u2ehi3]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h173, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p182_1, u2ehi4]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h0, hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h1, h171, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p182_1, u2ehi2]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h0, h172, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p182_1, u2ehi3]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h0, h173, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p182_1, u2ehi4]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h1, hlam, p182_1]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h4, hlam, p182_1]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h172, h2, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p182_1, u2ehi3]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h0, h173, h3, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p182_1, u2ehi4]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h2, hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h5, hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h7, hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h9, hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h3, hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h6, hlam, p182_1]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h8, hlam, p182_0]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [h172, h2, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p182_1, u2ehi3]
                                    · have p182_0 := h182c.1
                                      have p182_1 := h182c.2.1
                                      have p182_2 := h182c.2.2.1
                                      have p182_3 := h182c.2.2.2
                                      linarith only [hlam, p182_0]
                              · linarith only [h177, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                          · linarith only [h171, h174, h7, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h171, h173, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h171, h172, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
                      · linarith only [h171, h212, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h212, h5, h9, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h215 | h215
                  · linarith only [h215, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h218 | h218
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h219 | h219
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h220 | h220
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
                            · linarith only [h2, h215, h221, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h224 | h224
                                · linarith only [h2, h215, h218, h224, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h226 | h226
                                  · linarith only [h2, h215, h217, h218, h223, h226, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · rcases h0bigk with h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h2, h218, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h2, h218, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h2, h218, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h0, hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h2, h218, h7, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h0, h2, h218, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h0, h2, h218, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h1, hlam, p228_1]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h4, hlam, p228_1]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h2, h218, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h8, hlam, p228_1]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h2, hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h5, hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h7, hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h215, hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h3, hlam, p228_0]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h6, hlam, p228_1]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h1, h217, h223, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p228_1]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [h2, h218, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1, u2ehi3]
                                    · have p228_0 := h228c.1
                                      have p228_1 := h228c.2.1
                                      have p228_2 := h228c.2.2.1
                                      have p228_3 := h228c.2.2.2
                                      linarith only [hlam, p228_0]
                              · linarith only [h223, h7, h8, hc35, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h220, h7, h8, hc13, hc35, hlam, hphi]
                        · linarith only [h217, h219, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h217, h218, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h217, h4, h8, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h259 | h259
                · rcases m.htr 0 4 5 (by decide) (by decide) with h260 | h260
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                          · linarith only [h1, h259, h264, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                              · linarith only [h259, h263, h267, h3, h7, hc23, hlam, hphi, u2ehi4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h269 | h269
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h270 | h270
                                  · rcases h0bigk with h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c | h271c
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [hlam, p271_0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h259, h263, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi4]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h259, h263, h3, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi4]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h263, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi4]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h0, hlam, p271_0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [hlam, p271_0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h259, h263, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi4]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h0, h259, h263, h3, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi4]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h0, h263, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi4]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h1, hlam, p271_1]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h4, hlam, p271_1]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [hlam, p271_0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h7, hlam, p271_1]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h263, h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi4]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h2, hlam, p271_0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h5, hlam, p271_0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi2]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [hlam, p271_0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h263, h3, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p271_1, u2ehi4]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h3, hlam, p271_0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h6, hlam, p271_1]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h259, hlam, p271_0]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [h260, hlam, p271_1]
                                    · have p271_0 := h271c.1
                                      have p271_1 := h271c.2.1
                                      have p271_2 := h271c.2.2.1
                                      have p271_3 := h271c.2.2.2
                                      linarith only [hlam, p271_0]
                                  · linarith only [h259, h263, h270, h3, h7, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                · linarith only [h259, h266, h269, h3, h7, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h260, h262, h266, h7, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h259, h263, h6, h7, hc34, hlam, hphi, ht23, u2ehi1]
                      · linarith only [h261, h262, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h261, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h259, h260, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h306 | h306
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h308 | h308
                          · linarith only [h1, h308, h7, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h310 | h310
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                              · linarith only [h0, h2, h305, h310, h311, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h313 | h313
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h314 | h314
                                  · rcases h0bigk with h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c | h315c
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u2ehi0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h305, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u2ehi2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h259, h304, h305, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u2ehi2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h259, h305, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u2ehi2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h0, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h305, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u2ehi2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h0, h1, h259, h304, h305, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u2ehi2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h0, h1, h259, h305, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u2ehi2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, hlam, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h4, hlam, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h7, hlam, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h259, hlam, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h2, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h5, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h305, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u2ehi2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h259, h305, h7, hc34, hlam, hphi, ht23, p315_1, u2ehi2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h3, hlam, p315_0]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h6, hlam, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h1, h305, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p315_1, u2ehi2]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [h304, hlam, p315_1]
                                    · have p315_0 := h315c.1
                                      have p315_1 := h315c.2.1
                                      have p315_2 := h315c.2.2.1
                                      have p315_3 := h315c.2.2.2
                                      linarith only [hlam, p315_0]
                                  · linarith only [h1, h305, h314, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h2, h310, h313, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h304, h306, h310, h7, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h0, h305, h307, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h305, h306, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h305, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h348 | h348
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h349 | h349
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h350 | h350
                          · linarith only [h1, h350, h7, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h352 | h352
                            · linarith only [h1, h2, h304, h347, h352, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h354 | h354
                              · linarith only [h1, h347, h354, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h356 | h356
                                · linarith only [h0, h304, h348, h356, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h358 | h358
                                  · linarith only [h1, h304, h347, h358, h7, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h1, h347, h358, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h0, h347, h349, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h347, h348, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h347, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
          · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h366 | h366
          · linarith only [h366, h4, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h368 | h368
            · linarith only [h368, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h370 | h370
              · rcases m.htr 0 3 5 (by decide) (by decide) with h371 | h371
                · rcases m.htr 0 4 5 (by decide) (by decide) with h372 | h372
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                    · linarith only [h0, h373, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h375 | h375
                      · linarith only [h0, h366, h375, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                        · linarith only [h0, h368, h377, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h379 | h379
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h380 | h380
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h381 | h381
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
                                  · rcases h0bigk with h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c | h384c
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h1, h379, h383, hc01, hc45, hlam, hphi, ht0b, ht5b, p384_1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, h366, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, h368, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h4, hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h366, hlam, p384_1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h368, hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h1, hlam, p384_1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, h366, h4, hc23, hlam, hphi, p384_1, u2ehi1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, h368, h4, hc23, hlam, hphi, p384_1, u2ehi1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h2, hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h370, hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, h368, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h3, hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p384_1, u2ehi1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h371, hlam, p384_0]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [h372, hlam, p384_1]
                                    · have p384_0 := h384c.1
                                      have p384_1 := h384c.2.1
                                      have p384_2 := h384c.2.2.1
                                      have p384_3 := h384c.2.2.2
                                      linarith only [hlam, p384_0]
                                  · rcases h0bigk with h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c | h410c
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h1, h379, h380, h383, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p410_1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h2, h380, h383, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p410_1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h0, h368, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h0, hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h4, hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h366, hlam, p410_1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h368, hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h1, hlam, p410_1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h0, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h2, h380, h383, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p410_1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h0, h368, h4, hc23, hlam, hphi, p410_1, u2ehi1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h2, hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h0, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h370, hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h0, h366, h368, h381, hc23, hlam, hphi, p410_1, u2ehi1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h3, hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p410_1, u2ehi1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h371, hlam, p410_0]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [h372, hlam, p410_1]
                                    · have p410_0 := h410c.1
                                      have p410_1 := h410c.2.1
                                      have p410_2 := h410c.2.2.1
                                      have p410_3 := h410c.2.2.2
                                      linarith only [hlam, p410_0]
                                · linarith only [h1, h379, h380, h382, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h0, h381, h4, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h370, h372, h375, h380, h4, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h370, h373, h379, h4, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h440 | h440
                    · linarith only [h0, h366, h440, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h442 | h442
                      · linarith only [h0, h366, h442, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h444 | h444
                        · linarith only [h0, h4, h444, hc23, hlam, hphi, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h446 | h446
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h447 | h447
                            · linarith only [h1, h366, h372, h446, h447, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h449 | h449
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h450 | h450
                                · linarith only [h0, h366, h372, h450, hc24, hlam, hphi, u2ehi1]
                                · linarith only [h0, h366, h450, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h0, h4, h449, hc34, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h370, h372, h440, h446, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h455 | h455
                  · linarith only [h370, h371, h455, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
                    · linarith only [h0, h4, h457, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h459 | h459
                      · linarith only [h0, h366, h459, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
                        · linarith only [h0, h368, h461, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h464 | h464
                            · linarith only [h0, h1, h366, h455, h463, h464, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h467 | h467
                                · linarith only [h0, h366, h455, h466, h467, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h366, h467, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h1, h463, h466, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h370, h371, h463, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h472 | h472
                · rcases m.htr 0 4 5 (by decide) (by decide) with h473 | h473
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h474 | h474
                    · linarith only [h0, h4, h474, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h476 | h476
                      · linarith only [h0, h4, h476, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h478 | h478
                        · linarith only [h0, h368, h478, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h480 | h480
                          · linarith only [h1, h370, h480, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h482 | h482
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                              · linarith only [h368, h370, h472, h483, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h0, h4, h483, hc34, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h366, h473, h476, h482, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h370, h472, h473, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                    · linarith only [h0, h4, h489, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h491 | h491
                      · linarith only [h0, h4, h491, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h493 | h493
                        · linarith only [h1, h472, h489, h493, hc35, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h495 | h495
                          · linarith only [h1, h370, h495, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h497 | h497
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
                              · linarith only [h370, h4, h498, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h4, h498, hc34, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h370, h488, h489, h495, h497, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
                    · linarith only [h0, h4, h502, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
                      · linarith only [h0, h4, h504, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h506 | h506
                        · linarith only [h0, h368, h506, hlam]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h508 | h508
                          · linarith only [h1, h370, h4, h508, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h510 | h510
                            · linarith only [h0, h2, h370, h4, h488, h510, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h512 | h512
                              · linarith only [h0, h370, h4, h512, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h0, h4, h512, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h515 | h515
        · rcases m.htr 0 2 4 (by decide) (by decide) with h516 | h516
          · rcases m.htr 0 2 5 (by decide) (by decide) with h517 | h517
            · linarith only [h0, h3, h517, hlam]
            · linarith only [h515, h517, hc25, hlam, hphi, u2ehi2]
          · linarith only [h515, h516, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h521 | h521
          · linarith only [h515, h521, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h523 | h523
            · linarith only [h515, h523, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h525 | h525
              · rcases m.htr 0 3 5 (by decide) (by decide) with h526 | h526
                · linarith only [h1, h3, h526, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
                  · linarith only [h0, h3, h525, h526, h528, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h530 | h530
                    · linarith only [h0, h521, h525, h526, h530, hc35, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h532 | h532
                      · linarith only [h1, h3, h521, h530, h532, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h534 | h534
                        · linarith only [h0, h515, h534, hc23, hlam, hphi, u2ehi4]
                        · linarith only [h1, h3, h530, h534, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h537 | h537
                · linarith only [h0, h3, h525, h537, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h539 | h539
                  · linarith only [h2, h3, h539, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h541 | h541
                    · linarith only [h0, h3, h541, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h543 | h543
                      · linarith only [h1, h3, h521, h541, h543, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h545 | h545
                        · linarith only [h0, h515, h545, hc23, hlam, hphi, u2ehi4]
                        · linarith only [h1, h3, h541, h545, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h548 | h548
      · rcases m.htr 0 2 3 (by decide) (by decide) with h549 | h549
        · rcases m.htr 0 2 4 (by decide) (by decide) with h550 | h550
          · linarith only [h0, h2, h550, hlam]
          · linarith only [h549, h550, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h553 | h553
          · linarith only [h549, h553, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h555 | h555
            · linarith only [h549, h555, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h557 | h557
              · linarith only [h1, h2, h557, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h559 | h559
                · rcases m.htr 0 4 5 (by decide) (by decide) with h560 | h560
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h561 | h561
                    · linarith only [h0, h2, h549, h561, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h563 | h563
                      · linarith only [h0, h549, h563, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h1, h2, h561, h563, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h560, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h567 | h567
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
                    · linarith only [h0, h2, h568, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h570 | h570
                      · linarith only [h1, h2, h568, h570, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1, h2, h568, h570, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h567, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h574 | h574
        · rcases m.htr 0 2 4 (by decide) (by decide) with h575 | h575
          · linarith only [h0, h2, h575, hlam]
          · linarith only [h574, h575, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h578 | h578
          · linarith only [h574, h578, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h580 | h580
            · linarith only [h574, h580, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h582 | h582
              · linarith only [h1, h2, h582, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h584 | h584
                · linarith only [h0, h548, h582, h584, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h586 | h586
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h587 | h587
                    · linarith only [h0, h574, h587, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h589 | h589
                      · linarith only [h1, h548, h587, h589, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1, h2, h587, h589, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h586, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h593 | h593
    · rcases m.htr 0 1 5 (by decide) (by decide) with h594 | h594
      · rcases m.htr 0 2 3 (by decide) (by decide) with h595 | h595
        · linarith only [h0, h1, h595, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h597 | h597
          · linarith only [h595, h597, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h599 | h599
            · linarith only [h595, h599, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h601 | h601
              · rcases m.htr 0 3 5 (by decide) (by decide) with h602 | h602
                · rcases m.htr 0 4 5 (by decide) (by decide) with h603 | h603
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
                    · linarith only [h0, h595, h604, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h604, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h607 | h607
                    · linarith only [h0, h1, h607, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h607, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h602, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h601, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h612 | h612
        · linarith only [h0, h1, h612, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h614 | h614
          · linarith only [h612, h614, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h616 | h616
            · linarith only [h612, h616, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h618 | h618
              · rcases m.htr 0 3 5 (by decide) (by decide) with h619 | h619
                · rcases m.htr 0 4 5 (by decide) (by decide) with h620 | h620
                  · linarith only [h593, h594, h620, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
                    · linarith only [h0, h1, h622, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h622, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h619, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h618, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h627 | h627
      · rcases m.htr 0 2 3 (by decide) (by decide) with h628 | h628
        · linarith only [h0, h1, h628, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h630 | h630
          · linarith only [h628, h630, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h632 | h632
            · linarith only [h628, h632, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h634 | h634
              · rcases m.htr 0 3 5 (by decide) (by decide) with h635 | h635
                · rcases m.htr 0 4 5 (by decide) (by decide) with h636 | h636
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
                    · linarith only [h0, h1, h628, h637, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h637, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h593, h636, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h593, h634, h635, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h634, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h643 | h643
        · linarith only [h0, h1, h643, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h645 | h645
          · linarith only [h643, h645, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h647 | h647
            · linarith only [h643, h647, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h649 | h649
              · rcases m.htr 0 3 5 (by decide) (by decide) with h650 | h650
                · rcases m.htr 0 4 5 (by decide) (by decide) with h651 | h651
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h652 | h652
                    · linarith only [h0, h1, h643, h652, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h0, h1, h652, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h593, h651, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h593, h649, h650, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h649, hc34, hlam, hphi, ht23, u2ehi1]

end R2N4
