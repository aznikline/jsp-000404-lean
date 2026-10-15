import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_H_I_L_0_L_R_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2bigk := hb2.1
  have h3elo := hb3.1
  have h5ehi := hb5.1
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
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h5, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h11, h8, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h11, h13, h8, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · rcases h2bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht5b, p15_1, u5ehi1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 2) (by simp) with h19 | h19
                          · rcases p15_3 (m.d 1 2) (by simp) with h20 | h20
                            · linarith only [h0, h20, hlam]
                            · linarith only [h20, h6, hlam]
                          · linarith only [h19, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, hlam, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h8, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h8, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h5, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p15_1, u3elo2]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h9, hlam, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h2, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h6, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h8, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h11, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h3, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h7, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h7, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                · linarith only [h4, h8, hc23, hlam, hphi, u3elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                · linarith only [h0, h3, h46, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h4, h46, hc23, hlam, hphi, u3elo0]
            · linarith only [h2, h4, h5, h6, hc23, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
            · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
              · linarith only [h1, h5, h51, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                    · linarith only [h1, h50, h51, h54, h55, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
                      · linarith only [h50, h51, h53, h55, h57, hlam]
                      · rcases h2bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h0, h50, h53, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h0, h50, h51, h53, h54, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          rcases p59_3 (m.d 0 2) (by simp) with h63 | h63
                          · rcases p59_3 (m.d 1 2) (by simp) with h64 | h64
                            · linarith only [h0, h64, hlam]
                            · linarith only [h50, h64, hlam]
                          · linarith only [h63, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h0, h50, h51, h53, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h0, hlam, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h5, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h1, h51, h53, h54, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p59_1, u3elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h51, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h1, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h1, hc12, hlam, hphi, ht23, p59_1, u3elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h1, h53, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p59_1, u3elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h1, h51, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p59_1, u3elo0, u5ehi1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h2, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h50, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h53, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h55, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h3, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h50, h53, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p59_1]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h54, hlam, p59_0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [h1, h53, h54, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p59_1, u3elo0]
                        · have p59_0 := h59c.1
                          have p59_1 := h59c.2.1
                          have p59_2 := h59c.2.2.1
                          have p59_3 := h59c.2.2.2
                          linarith only [hlam, p59_0]
                  · linarith only [h5, h50, h53, h54, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h5, h53, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h91 | h91
              · linarith only [h5, h91, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h1, h93, h96, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                      · rcases h2bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          rcases p98_3 (m.d 0 2) (by simp) with h100 | h100
                          · rcases p98_3 (m.d 1 2) (by simp) with h101 | h101
                            · linarith only [h0, h101, hlam]
                            · rcases p98_3 (m.d 2 3) (by simp) with h103 | h103
                              · linarith only [h1, h103, hlam]
                              · linarith only [h103, h5, hlam]
                          · linarith only [h0, h100, hlam]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h0, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h0, h95, h96, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p98_1, u5ehi2]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h0, hlam, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h5, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h50, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h91, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h1, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h1, h95, h96, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p98_1, u3elo0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h1, h91, hc12, hlam, hphi, ht23, p98_1, u3elo0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h2, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h93, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h2, h4, h91, hc12, hlam, hphi, ht23, p98_1, u3elo0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h3, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h94, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h95, hlam, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                      · linarith only [h130, h4, h50, h95, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                      · rcases h2bigk with h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          rcases p132_3 (m.d 0 2) (by simp) with h134 | h134
                          · rcases p132_3 (m.d 1 2) (by simp) with h135 | h135
                            · linarith only [h0, h135, hlam]
                            · rcases p132_3 (m.d 2 3) (by simp) with h137 | h137
                              · linarith only [h1, h137, hlam]
                              · linarith only [h137, h5, hlam]
                          · linarith only [h0, h134, hlam]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h94, hc01, hlam, hphi, ht0b, ht5b, p132_1, u5ehi2]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h50, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p132_1, u5ehi2]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, hlam, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h5, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h50, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h91, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h1, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hc12, hc23, hlam, hphi, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h1, h50, hc12, hlam, hphi, ht23, p132_1, u3elo0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h1, h91, hc12, hlam, hphi, ht23, p132_1, u3elo0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h2, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h93, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h95, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h3, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h94, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h1, h50, h94, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p132_1, u3elo0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                  · linarith only [h5, h94, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h5, h93, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
          · rcases m.htr 1 2 4 (by decide) (by decide) with h167 | h167
            · rcases m.htr 1 2 5 (by decide) (by decide) with h168 | h168
              · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                · linarith only [h169, h4, hc03, hlam, hphi, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h171 | h171
                  · linarith only [h0, h167, h169, h171, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
                    · linarith only [h0, h167, h173, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                      · linarith only [h169, h173, h175, hc23, hlam, hphi, u3elo3]
                      · rcases h2bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h0, h168, hc01, hlam, hphi, ht0b, ht5b, p177_1, u5ehi2]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          rcases p177_3 (m.d 0 2) (by simp) with h180 | h180
                          · rcases p177_3 (m.d 1 2) (by simp) with h181 | h181
                            · linarith only [h0, h181, hlam]
                            · linarith only [h166, h181, hlam]
                          · linarith only [h180, hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          rcases p177_3 (m.d 0 2) (by simp) with h185 | h185
                          · rcases p177_3 (m.d 1 2) (by simp) with h186 | h186
                            · linarith only [h0, h186, hlam]
                            · linarith only [h167, h186, hlam]
                          · linarith only [h185, hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p177_1, u5ehi2]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h0, hlam, p177_1]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p177_1]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h0, h169, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p177_1]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p177_1, u5ehi2]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h1, hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h166, hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h169, hlam, p177_1]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h171, hlam, p177_1]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h2, hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h167, hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h0, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p177_1]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h173, hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h3, hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h168, hlam, p177_0]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h0, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p177_1]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [h0, h168, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p177_1]
                        · have p177_0 := h177c.1
                          have p177_1 := h177c.2.1
                          have p177_2 := h177c.2.2.1
                          have p177_3 := h177c.2.2.2
                          linarith only [hlam, p177_0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h211 | h211
                · linarith only [h166, h211, h4, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h213 | h213
                  · linarith only [h1, h213, h4, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · linarith only [h167, h168, h211, h213, hc23, hlam, hphi, u3elo4]
            · linarith only [h166, h167, h2, h4, hc23, hlam, hphi, u3elo3]
          · linarith only [h1, h166, h4, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h218 | h218
        · rcases m.htr 1 2 3 (by decide) (by decide) with h219 | h219
          · rcases m.htr 1 2 4 (by decide) (by decide) with h220 | h220
            · rcases m.htr 1 2 5 (by decide) (by decide) with h221 | h221
              · linarith only [h0, h221, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
                · rcases m.htr 2 3 5 (by decide) (by decide) with h224 | h224
                  · linarith only [h0, h219, h224, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                  · linarith only [h0, h219, h224, h3, hc23, hlam, hphi, u3elo4]
                · linarith only [h218, h223, hc23, hlam, hphi, u3elo0]
            · linarith only [h2, h219, h220, h3, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h1, h219, h3, hc12, hc25, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
          · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
            · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
              · linarith only [h0, h232, h3, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                · linarith only [h1, h218, h234, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h1, h218, h236, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                  · linarith only [h1, h236, h3, hc23, hlam, hphi, u3elo4]
            · linarith only [h2, h231, h3, hc12, hc25, hlam, hphi]
          · linarith only [h1, h230, h3, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h241 | h241
      · rcases m.htr 0 3 4 (by decide) (by decide) with h242 | h242
        · linarith only [h1, h2, h242, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h244 | h244
          · rcases m.htr 1 2 4 (by decide) (by decide) with h245 | h245
            · linarith only [h0, h2, h245, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h247 | h247
              · rcases m.htr 2 3 4 (by decide) (by decide) with h248 | h248
                · linarith only [h0, h2, h242, h244, h248, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h2, h244, h248, hc23, hlam, hphi, u3elo3]
              · linarith only [h2, h241, h247, hc12, hc24, hlam, hphi]
          · linarith only [h1, h2, h242, h244, hc12, hlam, hphi, ht23, u3elo3]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h253 | h253
        · linarith only [h1, h2, h253, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
          · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
            · linarith only [h0, h2, h256, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
              · linarith only [h0, h241, h258, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h260 | h260
                · linarith only [h0, h2, h253, h255, h260, hlam]
                · linarith only [h0, h2, h255, h260, hc23, hlam, hphi, u3elo3]
          · linarith only [h1, h2, h255, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h264 | h264
    · rcases m.htr 0 2 5 (by decide) (by decide) with h265 | h265
      · linarith only [h1, h265, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h267 | h267
        · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
          · linarith only [h0, h1, h264, h268, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
            · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
              · linarith only [h0, h265, h271, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h273 | h273
                · rcases m.htr 2 3 5 (by decide) (by decide) with h274 | h274
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h275 | h275
                    · linarith only [h0, h265, h270, h274, h275, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h277 | h277
                      · linarith only [h0, h265, h270, h273, h275, h277, hlam]
                      · rcases h2bigk with h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h265, h270, h273, h274, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p279_1, u3elo2]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h1, hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h265, h273, h274, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p279_1, u3elo2]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h265, hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h0, hlam, p279_1]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h268, hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h268, h273, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p279_1, u3elo1]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h271, hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p279_1, u3elo2]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, p279_1, u3elo2]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h273, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p279_1, u3elo2]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h265, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p279_1, u3elo2, u5ehi0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h264, hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h270, hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h273, hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h275, hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h0, h270, h273, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p279_1]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h270, h273, h275, hc34, hc45, hlam, hphi, p279_1]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h274, hlam, p279_0]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [h273, h274, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p279_1, u3elo2]
                        · have p279_0 := h279c.1
                          have p279_1 := h279c.2.1
                          have p279_2 := h279c.2.2.1
                          have p279_3 := h279c.2.2.2
                          linarith only [hlam, p279_0]
                  · linarith only [h0, h1, h270, h273, h274, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                · linarith only [h0, h1, h270, h273, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
            · linarith only [h1, h264, h270, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h1, h264, h267, hlam]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h309 | h309
      · linarith only [h1, h309, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h311 | h311
        · rcases m.htr 1 2 3 (by decide) (by decide) with h312 | h312
          · linarith only [h0, h1, h312, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h314 | h314
            · linarith only [h0, h264, h314, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
              · linarith only [h0, h309, h316, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h318 | h318
                · rcases m.htr 2 3 5 (by decide) (by decide) with h319 | h319
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h320 | h320
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h321 | h321
                      · linarith only [h311, h321, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0, u5ehi4]
                      · rcases h2bigk with h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h309, h318, h320, hc12, hc23, hlam, hphi, p323_1]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h1, hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h264, hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h309, hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h0, hlam, p323_1]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h312, hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h314, hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h316, hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p323_1, u3elo2]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, p323_1, u3elo2]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h320, h321, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p323_1, u3elo2]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p323_1, u3elo2, u5ehi2]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p323_1]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p323_1]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h318, hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h0, h309, h318, hc12, hlam, hphi, ht23, p323_1, u3elo2]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p323_1]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p323_1]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h319, hlam, p323_0]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [h320, hlam, p323_1]
                        · have p323_0 := h323c.1
                          have p323_1 := h323c.2.1
                          have p323_2 := h323c.2.2.1
                          have p323_3 := h323c.2.2.2
                          linarith only [hlam, p323_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h349 | h349
                      · linarith only [h0, h264, h320, h349, hc12, hlam, hphi, ht23, u3elo3]
                      · rcases h2bigk with h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c | h351c
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h264, hc12, hc24, hlam, hphi, p351_1]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h1, hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h264, hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h309, hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h0, hlam, p351_1]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h312, hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h314, hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h316, hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p351_1, u3elo2]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, p351_1, u3elo2]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p351_1, u3elo2]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p351_1, u3elo2, u5ehi2]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h0, hc12, hc24, hlam, hphi, p351_1]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hc12, hc24, hlam, hphi, p351_1]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h318, hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h320, hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h0, hc12, hc25, hlam, hphi, p351_1]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hc12, hc25, hlam, hphi, p351_1]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h319, hlam, p351_0]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [h319, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p351_1, u3elo2]
                        · have p351_0 := h351c.1
                          have p351_1 := h351c.2.1
                          have p351_2 := h351c.2.2.1
                          have p351_3 := h351c.2.2.2
                          linarith only [hlam, p351_0]
                  · linarith only [h0, h1, h319, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h1, h311, h318, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
          · linarith only [h0, h1, h379, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h381 | h381
            · linarith only [h0, h264, h381, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h383 | h383
              · linarith only [h0, h1, h383, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h385 | h385
                · linarith only [h1, h311, h385, hc02, hlam, hphi, ht23, u3elo2]
                · linarith only [h0, h1, h385, hc12, hlam, hphi, ht23, u3elo3]

end R2N4
