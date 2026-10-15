import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_IR_L_R_L_I_L_R_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0ehi := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2ehi := hb2.1
  have h5ehi := hb5.1
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
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                            · linarith only [h0, h10, h14, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                              · linarith only [h0, h11, h16, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h11, h13, h16, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                            · linarith only [h0, h10, h19, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                              · linarith only [h0, h11, h13, h21, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c | h23c
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h19, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h19, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23_1, u2ehi2]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hc01, hlam, hphi, p23_1, u0ehi3]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hc01, hlam, hphi, p23_1, u0ehi4]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, hlam, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h19, h8, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p23_1, u2ehi2]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h9, hc01, hlam, hphi, p23_1, u0ehi4]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, p23_1, u0ehi4]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h1, hlam, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h4, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h9, hc03, hlam, hphi, p23_1, u0ehi4]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h0, h4, hc01, hlam, hphi, p23_1, u0ehi4]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h2, hlam, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h5, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h7, hlam, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hc04, hlam, hphi, p23_1, u0ehi4]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h3, hlam, p23_1]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h6, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h8, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [h9, hlam, p23_0]
                                · have p23_0 := h23c.1
                                  have p23_1 := h23c.2.1
                                  have p23_2 := h23c.2.2.1
                                  have p23_3 := h23c.2.2.2
                                  linarith only [hlam, p23_0]
                        · linarith only [h10, h12, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h10, h11, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h51 | h51
                      · linarith only [h10, h51, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h53 | h53
                        · linarith only [h0, h10, h4, h53, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h57 | h57
                              · rcases h0bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [hlam, p58_0]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h4, h53, h56, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p58_1, u2ehi1]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [hc01, hlam, hphi, p58_1, u0ehi2]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [hc01, hlam, hphi, p58_1, u0ehi3]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [hc01, hlam, hphi, p58_1, u0ehi4]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h0, hlam, p58_1]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [hlam, p58_0]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h2, h55, h7, hc02, hlam, hphi, ht0b, ht5b, p58_1, u5ehi4]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h0, h2, h55, hc01, hlam, hphi, ht0b, ht5b, p58_1, u5ehi4]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, p58_1, u0ehi4]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h1, hlam, p58_1]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h4, hlam, p58_0]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [hlam, p58_0]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h5, h53, h57, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p58_1, u2ehi1]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h0, h4, h53, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p58_1, u2ehi1]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h2, hlam, p58_1]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h5, hlam, p58_0]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h7, hlam, p58_1]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [hlam, p58_0]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h53, h6, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p58_1, u2ehi1]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h3, hlam, p58_1]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h6, hlam, p58_0]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h8, hlam, p58_0]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [h9, hlam, p58_0]
                                · have p58_0 := h58c.1
                                  have p58_1 := h58c.2.1
                                  have p58_2 := h58c.2.2.1
                                  have p58_3 := h58c.2.2.2
                                  linarith only [hlam, p58_0]
                              · linarith only [h2, h55, h57, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h0, h10, h4, h56, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h86 | h86
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                              · linarith only [h0, h5, h51, h55, h87, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h51, h87, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                            · linarith only [h0, h10, h4, h8, h86, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                          · linarith only [h9, h94, hc14, hlam, hphi, ht01, u0ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                            · linarith only [h0, h91, h96, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                              · linarith only [h9, h92, h98, hc14, hlam, hphi, ht01, u0ehi3]
                              · rcases h0bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h4, h8, h96, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h8, h96, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p100_1, u2ehi2]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hc01, hlam, hphi, p100_1, u0ehi3]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hc01, hlam, hphi, p100_1, u0ehi4]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h0, hlam, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h8, h96, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p100_1, u2ehi2]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, p100_1, u0ehi3]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, p100_1, u0ehi4]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h1, hlam, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h4, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hc03, hlam, hphi, p100_1, u0ehi3]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h0, h4, hc01, hlam, hphi, p100_1, u0ehi4]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h2, hlam, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h5, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h7, hlam, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h9, hlam, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h3, hlam, p100_1]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h6, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [h8, hlam, p100_0]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hc05, hlam, hphi, p100_1, u0ehi3]
                                · have p100_0 := h100c.1
                                  have p100_1 := h100c.2.1
                                  have p100_2 := h100c.2.2.1
                                  have p100_3 := h100c.2.2.2
                                  linarith only [hlam, p100_0]
                        · linarith only [h0, h6, h91, h93, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h91, h92, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h128 | h128
                      · linarith only [h128, h91, hc23, hlam, hphi, u2ehi3]
                      · linarith only [h128, h5, h9, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h131 | h131
                  · linarith only [h131, h7, h8, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h134 | h134
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h135 | h135
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                          · linarith only [h131, h136, h2, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h0, h133, h138, h8, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h140 | h140
                              · linarith only [h131, h134, h140, h2, hlam]
                              · rcases h0bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [hlam, p142_0]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [hc01, hlam, hphi, p142_1, u0ehi1]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h7, hc01, hlam, hphi, p142_1, u0ehi3]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [hc01, hlam, hphi, p142_1, u0ehi3]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h7, h8, hc01, hlam, hphi, p142_1, u0ehi3]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h0, hlam, p142_1]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [hlam, p142_0]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h7, hc02, hlam, hphi, p142_1, u0ehi3]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, p142_1, u0ehi3]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h0, h7, h8, hc01, hlam, hphi, p142_1, u0ehi3]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h1, hlam, p142_1]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h4, hlam, p142_0]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [hlam, p142_0]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [hc03, hlam, hphi, p142_1, u0ehi3]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h8, hlam, p142_1]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h2, hlam, p142_1]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h5, hlam, p142_0]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h7, hlam, p142_1]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [hlam, p142_0]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h131, hlam, p142_1]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h3, hlam, p142_1]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h6, hlam, p142_0]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [hc05, hlam, hphi, p142_1, u0ehi2]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [h131, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p142_1, u0ehi3]
                                · have p142_0 := h142c.1
                                  have p142_1 := h142c.2.1
                                  have p142_2 := h142c.2.2.1
                                  have p142_3 := h142c.2.2.2
                                  linarith only [hlam, p142_0]
                        · linarith only [h0, h133, h135, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h133, h134, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h133, h4, h8, hc35, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h171 | h171
                · rcases m.htr 0 4 5 (by decide) (by decide) with h172 | h172
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h175 | h175
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h176 | h176
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                            · linarith only [h0, h173, h177, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                            · linarith only [h171, h177, h7, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h171, h172, h174, h176, h7, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h174, h175, hc25, hlam, hphi, u2ehi3]
                      · linarith only [h0, h173, h174, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h173, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h171, h172, h7, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h185 | h185
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h187 | h187
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h188 | h188
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                            · linarith only [h171, h186, h190, hc12, hlam, hphi, ht01, u0ehi2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                              · linarith only [h0, h187, h192, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h189, h192, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h185, h187, h189, h7, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h186, h188, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h186, h187, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h171, h186, h4, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h200 | h200
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                          · linarith only [h185, h202, h7, hc14, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                            · linarith only [h1, h171, h199, h204, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                              · linarith only [h0, h185, h200, h206, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hc01, hlam, hphi, p208_1, u0ehi1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hc01, hlam, hphi, p208_1, u0ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h7, hc01, hlam, hphi, p208_1, u0ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h185, h7, hc01, hlam, hphi, p208_1, u0ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h0, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hc02, hlam, hphi, p208_1, u0ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h0, h7, hc01, hlam, hphi, p208_1, u0ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h0, h185, h7, hc01, hlam, hphi, p208_1, u0ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h1, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h4, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h7, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h171, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h2, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h5, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hc04, hlam, hphi, p208_1, u0ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h185, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h3, hlam, p208_1]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h6, hlam, p208_0]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h171, hc35, hlam, hphi, ht01, ht12, ht23, p208_1, u0ehi2]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [h185, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p208_1, u0ehi3]
                                · have p208_0 := h208c.1
                                  have p208_1 := h208c.2.1
                                  have p208_2 := h208c.2.2.1
                                  have p208_3 := h208c.2.2.2
                                  linarith only [hlam, p208_0]
                        · linarith only [h0, h199, h201, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h199, h200, hc24, hlam, hphi, u2ehi2]
                    · linarith only [h199, h4, h7, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h4, h6, hc25, hlam, hphi, u2ehi2]
          · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h239 | h239
          · linarith only [h239, h4, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h241 | h241
            · linarith only [h241, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h243 | h243
              · rcases m.htr 0 3 5 (by decide) (by decide) with h244 | h244
                · rcases m.htr 0 4 5 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h246 | h246
                    · linarith only [h246, h4, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h248 | h248
                      · linarith only [h239, h248, hc12, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h250 | h250
                        · linarith only [h0, h241, h250, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h252 | h252
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h253 | h253
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h254 | h254
                              · rcases h0bigk with h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c | h255c
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [hlam, p255_0]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [hc01, hlam, hphi, p255_1, u0ehi1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h2, h243, h252, hc01, hlam, hphi, ht0b, ht5b, p255_1, u5ehi4]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h2, h252, hc01, hlam, hphi, ht0b, ht5b, p255_1, u5ehi4]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h241, hc01, hlam, hphi, p255_1, u0ehi1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h0, hlam, p255_1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [hlam, p255_0]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h4, hlam, p255_1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h239, hlam, p255_1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h241, hlam, p255_1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h1, hlam, p255_1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [hc03, hlam, hphi, p255_1, u0ehi1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [hlam, p255_0]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h2, h252, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p255_1, u5ehi4]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h241, h4, hc23, hlam, hphi, ht01, ht12, p255_1, u0ehi1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h2, hlam, p255_1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [hc04, hlam, hphi, p255_1, u0ehi1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h243, hlam, p255_1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [hlam, p255_0]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h241, h243, h4, hc23, hlam, hphi, ht01, ht12, p255_1, u0ehi1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h3, hlam, p255_1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [hc05, hlam, hphi, p255_1, u0ehi1]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h244, hlam, p255_0]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [h245, hlam, p255_0]
                                · have p255_0 := h255c.1
                                  have p255_1 := h255c.2.1
                                  have p255_2 := h255c.2.2.1
                                  have p255_3 := h255c.2.2.2
                                  linarith only [hlam, p255_0]
                              · linarith only [h2, h252, h254, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h244, h253, h4, hc03, hlam, hphi, u0ehi1]
                          · linarith only [h239, h245, h248, h252, hc24, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h284 | h284
                    · linarith only [h0, h244, h284, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h286 | h286
                      · linarith only [h0, h286, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
                        · linarith only [h0, h241, h288, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                          · linarith only [h239, h245, h290, hc14, hlam, hphi, ht01, u0ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                              · linarith only [h239, h245, h293, hc24, hlam, hphi, ht01, ht12, u0ehi1]
                              · linarith only [h239, h293, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1]
                            · linarith only [h292, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h297 | h297
                  · linarith only [h243, h244, h297, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h299 | h299
                    · linarith only [h0, h299, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
                      · linarith only [h0, h239, h301, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h303 | h303
                        · linarith only [h0, h241, h303, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h305 | h305
                          · linarith only [h2, h297, h305, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h307 | h307
                            · linarith only [h239, h243, h244, h307, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h307, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h310 | h310
                · rcases m.htr 0 4 5 (by decide) (by decide) with h311 | h311
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h312 | h312
                    · linarith only [h0, h312, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h314 | h314
                      · linarith only [h0, h239, h314, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
                        · linarith only [h0, h241, h316, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h318 | h318
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h319 | h319
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h320 | h320
                              · rcases h0bigk with h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c | h321c
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [hlam, p321_0]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [hc01, hlam, hphi, p321_1, u0ehi1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h310, hc01, hlam, hphi, ht0b, ht5b, p321_1, u5ehi3]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h243, h310, hc01, hlam, hphi, ht0b, ht5b, p321_1, u5ehi3]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [hc01, hlam, hphi, p321_1, u0ehi4]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h0, hlam, p321_1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [hlam, p321_0]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h4, hlam, p321_1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h239, hlam, p321_1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h241, hlam, p321_1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h1, hlam, p321_1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [hc03, hlam, hphi, p321_1, u0ehi1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [hlam, p321_0]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h243, hlam, p321_0]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h241, h243, hc34, hlam, hphi, ht01, ht12, ht23, p321_1, u0ehi1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h2, hlam, p321_1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h243, hc34, hlam, hphi, ht01, ht12, ht23, p321_1, u0ehi1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h243, hc34, hlam, hphi, ht01, ht12, ht23, p321_1, u0ehi2]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [hlam, p321_0]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h241, h243, hc34, hlam, hphi, ht01, ht12, ht23, p321_1, u0ehi1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h3, hlam, p321_1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h310, hc03, hlam, hphi, p321_1, u0ehi1]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h310, hlam, p321_0]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [h311, hlam, p321_0]
                                · have p321_0 := h321c.1
                                  have p321_1 := h321c.2.1
                                  have p321_2 := h321c.2.2.1
                                  have p321_3 := h321c.2.2.2
                                  linarith only [hlam, p321_0]
                              · linarith only [h2, h318, h320, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · linarith only [h319, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h243, h310, h311, h314, h318, hc34, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h243, h310, h311, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h351 | h351
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
                    · linarith only [h0, h241, h352, hc25, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
                      · linarith only [h0, h310, h354, h4, hc35, hlam, hphi, ht23, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h356 | h356
                        · linarith only [h0, h310, h356, h4, hc35, hlam, hphi, ht23, u2ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h358 | h358
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h359 | h359
                            · linarith only [h310, h359, h4, hc23, hlam, hphi, u2ehi0]
                            · linarith only [h359, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h243, h351, h354, h358, hc34, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h363 | h363
                    · linarith only [h363, h4, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                      · linarith only [h0, h365, h4, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
                        · linarith only [h0, h241, h367, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
                          · linarith only [h243, h351, h369, h4, hc14, hlam, hphi, ht01, u0ehi1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h371 | h371
                            · linarith only [h310, h371, h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                            · linarith only [h371, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h374 | h374
        · rcases m.htr 0 2 4 (by decide) (by decide) with h375 | h375
          · rcases m.htr 0 2 5 (by decide) (by decide) with h376 | h376
            · linarith only [h0, h3, h376, hlam]
            · linarith only [h374, h376, hc25, hlam, hphi, u2ehi2]
          · linarith only [h374, h375, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h380 | h380
          · linarith only [h374, h380, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h382 | h382
            · linarith only [h374, h382, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h384 | h384
              · rcases m.htr 0 3 5 (by decide) (by decide) with h385 | h385
                · linarith only [h1, h3, h385, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h387 | h387
                  · linarith only [h0, h3, h384, h385, h387, hc35, hlam, hphi, ht23, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
                    · linarith only [h0, h380, h384, h385, h389, hc35, hlam, hphi, ht23, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                      · linarith only [h1, h3, h380, h389, h391, hc15, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h393 | h393
                        · linarith only [h1, h3, h382, h389, h393, hc15, hlam, hphi, ht01, u0ehi1]
                        · linarith only [h1, h3, h389, h393, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h396 | h396
                · linarith only [h0, h3, h384, h396, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h398 | h398
                  · linarith only [h2, h3, h398, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
                    · linarith only [h0, h374, h400, hc01, hlam, hphi, u0ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
                      · linarith only [h1, h3, h380, h400, h402, hc15, hlam, hphi, ht01, u0ehi1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                        · linarith only [h1, h3, h400, h404, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                        · linarith only [h1, h3, h400, h404, hc25, hlam, hphi, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h407 | h407
      · rcases m.htr 0 2 3 (by decide) (by decide) with h408 | h408
        · rcases m.htr 0 2 4 (by decide) (by decide) with h409 | h409
          · linarith only [h0, h2, h409, hlam]
          · linarith only [h408, h409, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h412 | h412
          · linarith only [h408, h412, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h414 | h414
            · linarith only [h412, h414, hc24, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h416 | h416
              · linarith only [h1, h2, h416, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h418 | h418
                · rcases m.htr 0 4 5 (by decide) (by decide) with h419 | h419
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h420 | h420
                    · linarith only [h0, h2, h420, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h422 | h422
                      · linarith only [h1, h2, h420, h422, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1, h2, h420, h422, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h419, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h426 | h426
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h427 | h427
                    · linarith only [h0, h408, h427, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
                      · linarith only [h1, h2, h427, h429, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                      · linarith only [h1, h2, h427, h429, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h426, hc45, hlam, hphi, ht23, ht34, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h433 | h433
        · rcases m.htr 0 2 4 (by decide) (by decide) with h434 | h434
          · linarith only [h0, h2, h434, hlam]
          · linarith only [h433, h434, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h437 | h437
          · linarith only [h433, h437, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h439 | h439
            · linarith only [h433, h439, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h441 | h441
              · linarith only [h1, h2, h441, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h443 | h443
                · linarith only [h0, h407, h441, h443, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h446 | h446
                    · linarith only [h0, h433, h446, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                      · linarith only [h1, h407, h437, h445, h446, h448, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                      · linarith only [h1, h2, h446, h448, hc24, hlam, hphi, u2ehi1]
                  · linarith only [h0, h2, h445, hc45, hlam, hphi, ht23, ht34, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h452 | h452
    · rcases m.htr 0 1 5 (by decide) (by decide) with h453 | h453
      · rcases m.htr 0 2 3 (by decide) (by decide) with h454 | h454
        · linarith only [h0, h1, h454, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h456 | h456
          · linarith only [h454, h456, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h458 | h458
            · linarith only [h454, h458, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h460 | h460
              · rcases m.htr 0 3 5 (by decide) (by decide) with h461 | h461
                · rcases m.htr 0 4 5 (by decide) (by decide) with h462 | h462
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h463 | h463
                    · linarith only [h0, h1, h463, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h463, hc23, hlam, hphi, u2ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h466 | h466
                    · linarith only [h0, h1, h466, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h466, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h461, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h460, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h471 | h471
        · linarith only [h0, h1, h471, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h473 | h473
          · linarith only [h471, h473, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h475 | h475
            · linarith only [h471, h475, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h477 | h477
              · rcases m.htr 0 3 5 (by decide) (by decide) with h478 | h478
                · rcases m.htr 0 4 5 (by decide) (by decide) with h479 | h479
                  · linarith only [h452, h453, h479, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h481 | h481
                    · linarith only [h0, h1, h481, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1, h481, hc23, hlam, hphi, u2ehi1]
                · linarith only [h0, h1, h478, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h477, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h486 | h486
      · rcases m.htr 0 2 3 (by decide) (by decide) with h487 | h487
        · linarith only [h0, h1, h487, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h489 | h489
          · linarith only [h487, h489, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h491 | h491
            · linarith only [h487, h491, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h493 | h493
              · rcases m.htr 0 3 5 (by decide) (by decide) with h494 | h494
                · rcases m.htr 0 4 5 (by decide) (by decide) with h495 | h495
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h496 | h496
                    · linarith only [h487, h496, hc12, hlam, hphi, ht01, u0ehi1]
                    · linarith only [h0, h1, h496, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h452, h495, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h1, h494, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h493, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h502 | h502
        · linarith only [h0, h1, h502, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h504 | h504
          · linarith only [h502, h504, hc23, hlam, hphi, u2ehi3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h506 | h506
            · linarith only [h502, h506, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h508 | h508
              · rcases m.htr 0 3 5 (by decide) (by decide) with h509 | h509
                · rcases m.htr 0 4 5 (by decide) (by decide) with h510 | h510
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
                    · linarith only [h502, h511, hc12, hlam, hphi, ht01, u0ehi1]
                    · linarith only [h0, h1, h511, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h452, h510, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                · linarith only [h0, h452, h508, h509, hc35, hlam, hphi, ht23, u2ehi1]
              · linarith only [h0, h1, h508, hc34, hlam, hphi, ht23, u2ehi1]

end R2N4
