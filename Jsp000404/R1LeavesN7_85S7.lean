import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_14_M_IR_L_0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4elo := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · rcases h1bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h10, h3, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h10, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          rcases p11_3 (m.d 0 1) (by simp) with h15 | h15
                          · rcases p11_3 (m.d 1 2) (by simp) with h16 | h16
                            · linarith only [h0, h16, hlam]
                            · linarith only [h16, h4, hlam]
                          · linarith only [h15, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          rcases p11_3 (m.d 0 1) (by simp) with h20 | h20
                          · rcases p11_3 (m.d 1 2) (by simp) with h21 | h21
                            · linarith only [h0, h21, hlam]
                            · linarith only [h21, h4, h7, hlam]
                          · linarith only [h20, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h10, h5, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi3]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h1, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h3, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h7, hc13, hlam, hphi, p11_1, u1ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p11_1, u1ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h2, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h4, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h5, hlam, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc14, hlam, hphi, p11_1, u1ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc15, hlam, hphi, p11_1, u1ehi0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h10, h2, h3, h5, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p11_1, u4elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h6, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h7, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                      · linarith only [h10, h2, h7, hc34, hlam, hphi, u4elo0]
                    · linarith only [h2, h7, h9, hc24, hlam, hphi, u4elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                      · rcases h1bigk with h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h3, h48, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h48, h5, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          rcases p49_3 (m.d 0 1) (by simp) with h53 | h53
                          · rcases p49_3 (m.d 1 2) (by simp) with h54 | h54
                            · linarith only [h0, h54, hlam]
                            · linarith only [h4, h54, hlam]
                          · linarith only [h53, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          rcases p49_3 (m.d 0 1) (by simp) with h58 | h58
                          · rcases p49_3 (m.d 1 2) (by simp) with h59 | h59
                            · linarith only [h0, h59, hlam]
                            · linarith only [h3, h48, h5, h59, h7, h8, hc23, hlam, hphi, ht34, u4elo1]
                          · linarith only [h58, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h48, h5, h8, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p49_1, u1ehi3]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p49_1, u1ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h1, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h3, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h7, hc13, hlam, hphi, p49_1, u1ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p49_1, u1ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h2, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h4, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h5, hlam, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hc14, hlam, hphi, p49_1, u1ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hc15, hlam, hphi, p49_1, u1ehi0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h2, h3, h48, h5, h7, h8, hc23, hlam, hphi, ht34, p49_1, u4elo0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h6, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h7, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                      · linarith only [h47, h48, hc34, hlam, hphi, u4elo2]
                    · linarith only [h2, h47, h7, hc24, hlam, hphi, u4elo0]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                · linarith only [h5, h6, h86, hlam]
                · linarith only [h86, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h5, hlam, hphi, ht12, ht23, ht34, u1ehi2, u4elo3]
          · linarith only [h4, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h91 | h91
          · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
            · rcases m.htr 1 3 5 (by decide) (by decide) with h93 | h93
              · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h97 | h97
                      · rcases h1bigk with h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c | h98c
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h91, h96, hc01, hc45, hlam, hphi, ht0b, ht5b, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h3, h91, h96, hc01, hc45, hlam, hphi, ht0b, ht5b, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          rcases p98_3 (m.d 0 1) (by simp) with h102 | h102
                          · rcases p98_3 (m.d 1 2) (by simp) with h103 | h103
                            · linarith only [h0, h103, hlam]
                            · linarith only [h103, h91, hlam]
                          · linarith only [h102, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          rcases p98_3 (m.d 0 1) (by simp) with h107 | h107
                          · rcases p98_3 (m.d 1 2) (by simp) with h108 | h108
                            · linarith only [h0, h108, hlam]
                            · linarith only [h108, h91, h94, hlam]
                          · linarith only [h107, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h0, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h3, hlam, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hc12, hlam, hphi, p98_1, u1ehi3]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h3, hc23, hlam, hphi, ht12, p98_1, u1ehi4]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h1, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h1, h91, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h1, h94, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p98_1, u1ehi4]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p98_1, u1ehi4]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h2, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h91, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h92, hlam, p98_1]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hc14, hlam, hphi, p98_1, u1ehi4]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hc15, hlam, hphi, p98_1, u1ehi0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h2, h91, h94, h96, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p98_1, u4elo0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h93, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [h94, hlam, p98_0]
                        · have p98_0 := h98c.1
                          have p98_1 := h98c.2.1
                          have p98_2 := h98c.2.2.1
                          have p98_3 := h98c.2.2.2
                          linarith only [hlam, p98_0]
                      · linarith only [h96, h97, hc34, hlam, hphi, u4elo2]
                    · linarith only [h2, h94, h96, hc24, hlam, hphi, u4elo0]
                  · linarith only [h1, h3, h93, h95, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h94, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h136 | h136
                · linarith only [h136, h3, h91, h93, hlam]
                · linarith only [h136, hlam, hphi, ht12, ht23, ht34, u1ehi3, u4elo4]
            · linarith only [h3, h92, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo3]
          · linarith only [h91, hlam, hphi, ht12, ht23, ht34, u1ehi1, u4elo2]
      · linarith only [h2, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h143 | h143
    · linarith only [h0, h143, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h145 | h145
      · linarith only [h0, h145, hc12, hlam, hphi, u1ehi3]
      · linarith only [h145, hlam, hphi, ht12, ht23, ht34, u1ehi0, u4elo1]

theorem r1l7_21_15_H_R_L_I (m : N7Model)
    (hb1 : CMSig2_7_H_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h5bigk := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h2, h7, hc01, hc45, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h10, h2, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h2, h5, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · rcases h5bigk with h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c | h15c
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi4]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 5) (by simp) with h18 | h18
                          · rcases p15_3 (m.d 1 5) (by simp) with h19 | h19
                            · linarith only [h1, h19, hlam]
                            · linarith only [h19, h4, hlam]
                          · linarith only [h18, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 5) (by simp) with h23 | h23
                          · rcases p15_3 (m.d 1 5) (by simp) with h24 | h24
                            · linarith only [h1, h24, hlam]
                            · linarith only [h0, h2, h24, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                          · linarith only [h23, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 5) (by simp) with h28 | h28
                          · rcases p15_3 (m.d 1 5) (by simp) with h29 | h29
                            · linarith only [h1, h29, hlam]
                            · linarith only [h29, h6, hlam]
                          · linarith only [h28, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 5) (by simp) with h35 | h35
                          · rcases p15_3 (m.d 1 5) (by simp) with h36 | h36
                            · rcases p15_3 (m.d 2 5) (by simp) with h37 | h37
                              · linarith only [h37, h4, hlam]
                              · rcases p15_3 (m.d 3 5) (by simp) with h39 | h39
                                · linarith only [h39, h8, hlam, p15_1]
                                · rcases p15_3 (m.d 4 5) (by simp) with h41 | h41
                                  · linarith only [h41, h6, hlam]
                                  · linarith only [h41, h9, hlam]
                            · linarith only [h36, h4, hlam]
                          · linarith only [h1, h35, hlam, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 5) (by simp) with h46 | h46
                          · rcases p15_3 (m.d 1 5) (by simp) with h47 | h47
                            · rcases p15_3 (m.d 2 5) (by simp) with h48 | h48
                              · linarith only [h4, h48, hlam]
                              · linarith only [h48, h8, hlam]
                            · linarith only [h47, hlam, p15_0]
                          · linarith only [h0, h1, h4, h46, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h2, h5, h6, h9, hc01, hc05, hlam, hphi, ht0b, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h4, hlam, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h2, h5, h6, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h9, hlam, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p15_1, u1ehi4]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h2, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi4]
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
                          linarith only [h13, hlam, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h1, h2, h5, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p15_1, u1ehi4]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h6, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc25, hlam, hphi, ht0b, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h2, h5, h6, hc01, hc35, hlam, hphi, ht0b, ht5b, p15_1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                    · linarith only [h69, h7, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h2, h5, h69, h71, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h2, h5, h6, h7, h71, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h74 | h74
                  · linarith only [h0, h2, h5, h7, h74, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h76 | h76
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h77 | h77
                      · rcases h5bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi4]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 5) (by simp) with h81 | h81
                          · rcases p78_3 (m.d 1 5) (by simp) with h82 | h82
                            · linarith only [h1, h82, hlam]
                            · linarith only [h4, h82, hlam]
                          · linarith only [h81, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 5) (by simp) with h86 | h86
                          · rcases p78_3 (m.d 1 5) (by simp) with h87 | h87
                            · linarith only [h1, h87, hlam]
                            · linarith only [h0, h2, h5, h77, h87, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                          · linarith only [h86, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 5) (by simp) with h91 | h91
                          · rcases p78_3 (m.d 1 5) (by simp) with h92 | h92
                            · linarith only [h1, h92, hlam]
                            · linarith only [h6, h92, hlam]
                          · linarith only [h91, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 5) (by simp) with h98 | h98
                          · rcases p78_3 (m.d 1 5) (by simp) with h99 | h99
                            · rcases p78_3 (m.d 2 5) (by simp) with h100 | h100
                              · linarith only [h100, h4, hlam]
                              · rcases p78_3 (m.d 3 5) (by simp) with h102 | h102
                                · linarith only [h0, h102, h2, h5, h77, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi4]
                                · linarith only [h102, h74, hlam]
                            · linarith only [h4, h99, hlam]
                          · linarith only [h1, h98, hlam, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, h74, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          rcases p78_3 (m.d 0 5) (by simp) with h108 | h108
                          · rcases p78_3 (m.d 1 5) (by simp) with h109 | h109
                            · rcases p78_3 (m.d 2 5) (by simp) with h110 | h110
                              · linarith only [h110, h4, hlam]
                              · linarith only [h110, h76, hlam]
                            · linarith only [h109, h6, hlam]
                          · linarith only [h1, h108, h76, hc24, hlam, hphi, ht12, u1ehi4]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, hc25, hlam, hphi, ht12, p78_1, u1ehi4]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h4, hlam, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h74, hlam, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p78_1, u1ehi4]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, h2, h5, h77, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p78_1, u1ehi4]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, h2, h5, h77, hc01, hc25, hlam, hphi, ht0b, ht5b, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h0, h2, h5, h77, hc01, hc45, hlam, hphi, ht0b, ht5b, p78_1]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h1, hc45, hlam, hphi, ht12, ht23, ht34, p78_1, u1ehi4]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h6, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h76, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [h77, hlam, p78_0]
                        · have p78_0 := h78c.1
                          have p78_1 := h78c.2.1
                          have p78_2 := h78c.2.2.1
                          have p78_3 := h78c.2.2.2
                          linarith only [hlam, p78_0]
                      · linarith only [h0, h4, h7, h76, h77, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                      · linarith only [h0, h131, h2, h5, h7, h76, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h131, h2, h5, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi3]
            · linarith only [h5, hc34, hlam, hphi, ht12, ht23, u1ehi2]
          · linarith only [h4, hc25, hlam, hphi, ht12, u1ehi1]
        · linarith only [h2, h3, hc24, hlam, hphi, ht12, u1ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht12, u1ehi1]
    · linarith only [h1, hc15, hlam, hphi, u1ehi0]
  · linarith only [h0, hc12, hlam, hphi, u1ehi0]

theorem r1l7_22_13_15_H_I_L_R_L_0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5elo := hb5.1
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 2 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 2 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 2 4 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 3 4 5 (by decide) (by decide) with h5 | h5
            · rcases h2bigk with h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c | h6c
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h1, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p6_1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p6_1, u3ehi2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, h4, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, h3, h4, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h2, h5, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, h4, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc12, hc23, hlam, hphi, p6_1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h1, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h2, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h0, h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p6_1, u3ehi4]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc02, hc25, hlam, hphi, p6_1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p6_1, u5elo2]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h3, hlam, p6_0]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [h4, hlam, p6_1]
              · have p6_0 := h6c.1
                have p6_1 := h6c.2.1
                have p6_2 := h6c.2.2.1
                have p6_3 := h6c.2.2.2
                linarith only [hlam, p6_0]
            · linarith only [h5, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
          · linarith only [h2, h4, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
        · linarith only [h3, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
        · linarith only [h2, h35, hc34, hlam, hphi, u3ehi4]
        · linarith only [h35, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
      · rcases m.htr 2 3 5 (by decide) (by decide) with h39 | h39
        · rcases m.htr 2 4 5 (by decide) (by decide) with h40 | h40
          · rcases m.htr 3 4 5 (by decide) (by decide) with h41 | h41
            · rcases h2bigk with h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c | h42c
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [hlam, p42_0]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                rcases p42_3 (m.d 0 2) (by simp) with h44 | h44
                · rcases p42_3 (m.d 1 2) (by simp) with h45 | h45
                  · linarith only [h45, hlam, p42_0]
                  · rcases p42_3 (m.d 2 3) (by simp) with h47 | h47
                    · linarith only [h47, hc12, hc23, hlam, hphi, p42_1]
                    · linarith only [h47, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1, u3ehi2]
                · linarith only [h44, hlam, p42_0]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1, u3ehi2]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h39, h40, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1, u3ehi4]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h39, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1, u3ehi4]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h1, hc02, hc24, hlam, hphi, p42_1]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [hlam, p42_0]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h1, h38, hlam, p42_1]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h1, hlam, p42_0]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h0, h1, h39, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1, u3ehi4]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [hc02, hc23, hlam, hphi, p42_1]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [hc12, hc23, hlam, hphi, p42_1]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [hlam, p42_0]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h1, hc12, hc23, hlam, hphi, p42_1]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h39, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p42_1, u3ehi4]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h0, hlam, p42_0]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h0, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p42_1]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h38, hlam, p42_0]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [hlam, p42_0]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h0, h39, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p42_1, u3ehi4]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [hc02, hc25, hlam, hphi, p42_1]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h0, h40, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p42_1]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h39, hlam, p42_0]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [h40, hlam, p42_1]
              · have p42_0 := h42c.1
                have p42_1 := h42c.2.1
                have p42_2 := h42c.2.2.1
                have p42_3 := h42c.2.2.2
                linarith only [hlam, p42_0]
            · linarith only [h41, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
          · linarith only [h1, h40, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h39, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
        · linarith only [h38, h77, hc34, hlam, hphi, u3ehi4]
        · linarith only [h77, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
    · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
      · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
        · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
          · rcases m.htr 3 4 5 (by decide) (by decide) with h84 | h84
            · rcases h2bigk with h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c | h85c
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hlam, p85_0]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h0, h80, hlam, p85_1]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p85_1, u3ehi2]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h0, hlam, p85_0]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h0, h80, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p85_1]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                rcases p85_3 (m.d 0 2) (by simp) with h91 | h91
                · linarith only [h91, hlam, p85_0]
                · rcases p85_3 (m.d 1 2) (by simp) with h93 | h93
                  · rcases p85_3 (m.d 2 3) (by simp) with h94 | h94
                    · linarith only [h94, hc02, hc23, hlam, hphi, p85_1]
                    · linarith only [h94, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p85_1, u3ehi2]
                  · linarith only [h93, hlam, p85_0]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hlam, p85_0]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h81, h84, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p85_1, u3ehi4]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h82, h83, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p85_1, u3ehi4]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h82, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p85_1, u3ehi4]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hc02, hc23, hlam, hphi, p85_1]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hc12, hc23, hlam, hphi, p85_1]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hlam, p85_0]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h82, h83, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p85_1, u3ehi4]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h82, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p85_1, u3ehi4]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h80, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p85_1]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h80, hlam, p85_0]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h81, hlam, p85_0]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hlam, p85_0]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h80, h82, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p85_1, u3ehi4]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hc02, hc25, hlam, hphi, p85_1]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p85_1, u5elo2]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h82, hlam, p85_0]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [h83, hlam, p85_1]
              · have p85_0 := h85c.1
                have p85_1 := h85c.2.1
                have p85_2 := h85c.2.2.1
                have p85_3 := h85c.2.2.2
                linarith only [hlam, p85_0]
            · linarith only [h84, hlam, hphi, ht34, ht45, u3ehi3, u5elo4]
          · linarith only [h0, h83, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h82, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h120 | h120
        · linarith only [h120, h81, hc34, hlam, hphi, u3ehi4]
        · linarith only [h120, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
      · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
        · rcases m.htr 2 4 5 (by decide) (by decide) with h125 | h125
          · rcases m.htr 3 4 5 (by decide) (by decide) with h126 | h126
            · rcases h2bigk with h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hlam, p127_0]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h0, hc12, hc24, hlam, hphi, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h0, h123, hlam, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h0, hlam, p127_0]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h0, h123, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h123, h80, hc02, hc23, hlam, hphi, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hlam, p127_0]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h123, h80, hlam, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h80, hlam, p127_0]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h123, h124, h80, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p127_1, u3ehi4]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hc02, hc23, hlam, hphi, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hc12, hc23, hlam, hphi, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hlam, p127_0]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h0, hc02, hc23, hlam, hphi, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h124, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p127_1, u3ehi4]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hc02, hc24, hlam, hphi, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hc12, hc24, hlam, hphi, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h123, hlam, p127_0]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hlam, p127_0]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h123, h124, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p127_1, u3ehi4]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hc02, hc25, hlam, hphi, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p127_1, u5elo2]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h124, hlam, p127_0]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [h125, hlam, p127_1]
              · have p127_0 := h127c.1
                have p127_1 := h127c.2.1
                have p127_2 := h127c.2.2.1
                have p127_3 := h127c.2.2.2
                linarith only [hlam, p127_0]
            · linarith only [h125, h126, hlam, hphi, ht34, ht45, u3ehi3, u5elo2]
          · linarith only [h0, h125, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
        · linarith only [h124, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]
      · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
        · linarith only [h123, h156, hc34, hlam, hphi, u3ehi4]
        · linarith only [h156, hlam, hphi, ht34, ht45, u3ehi2, u5elo3]

theorem r1l7_22_13_15_M_LI_L_R_L_R (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h5, h9, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                      · linarith only [h0, h11, h6, h9, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi4]
                      · linarith only [h0, h11, h5, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                    · linarith only [h14, h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h0, h14, h16, h6, h8, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h0, h18, h6, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h14, h18, h20, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h14, h20, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h4, h7, hc12, hlam, hphi, u2elo0]
              · linarith only [h5, h6, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
            · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h2, h4, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h28 | h28
        · rcases m.htr 0 2 5 (by decide) (by decide) with h29 | h29
          · linarith only [h2, h29, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
            · linarith only [h2, h31, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
              · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                · linarith only [h0, h2, h29, h34, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h36 | h36
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h37 | h37
                    · linarith only [h0, h29, h33, h37, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi3]
                    · linarith only [h31, h36, h37, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h40 | h40
                    · linarith only [h0, h2, h33, h40, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                    · linarith only [h0, h2, h33, h40, hlam]
              · linarith only [h2, h28, h33, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h44 | h44
          · linarith only [h2, h44, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
            · linarith only [h2, h46, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
              · linarith only [h0, h28, h48, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                · linarith only [h0, h1, h2, h44, h50, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h55 | h55
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h56 | h56
                          · linarith only [h53, h56, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi4]
                          · linarith only [h53, h55, h56, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                          · linarith only [h0, h28, h46, h52, h55, h59, hc12, hc34, hlam, hphi, u2elo2, u3ehi4]
                          · rcases h2bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h28, hc12, hlam, hphi, p61_1, u2elo3]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h2, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h28, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h44, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, hlam, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h46, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h48, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h50, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hc02, hlam, hphi, p61_1, u2elo2]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hc12, hlam, hphi, p61_1, u2elo2]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, h28, hc12, hlam, hphi, p61_1, u2elo2]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p61_1, u2elo2, u5ehi2]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p61_1, u2elo3]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hc12, hlam, hphi, p61_1, u2elo3]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h53, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h55, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p61_1, u2elo4]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hc12, hlam, hphi, p61_1, u2elo4]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h54, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, h28, h54, hc12, hlam, hphi, p61_1, u2elo2]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                      · linarith only [h46, h52, h54, hlam]
                    · linarith only [h46, h52, h53, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h90 | h90
                      · linarith only [h52, h90, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · linarith only [h89, h90, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h93 | h93
                      · linarith only [h89, h93, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h95 | h95
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                          · rcases h2bigk with h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [hc12, hlam, hphi, p97_1, u2elo0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h2, hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h28, hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h44, hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h0, hlam, p97_1]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h46, hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h48, hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h50, hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h93, h95, hc02, hlam, hphi, p97_1, u2elo3]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h93, h95, hc12, hlam, hphi, p97_1, u2elo3]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h89, hlam, p97_1]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h93, hlam, p97_1]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p97_1, u2elo3]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [hc12, hlam, hphi, p97_1, u2elo3]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p97_1, u2elo3, u3ehi0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [hlam, p97_0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h44, hlam, hphi, ht01, ht0b, ht12, ht5b, p97_1, u2elo3, u5ehi0]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, p97_1, u2elo4]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [hc12, hlam, hphi, p97_1, u2elo4]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h0, h2, hc12, hlam, hphi, p97_1, u2elo4]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [h95, hlam, p97_1]
                            · have p97_0 := h97c.1
                              have p97_1 := h97c.2.1
                              have p97_2 := h97c.2.2.1
                              have p97_3 := h97c.2.2.2
                              linarith only [hlam, p97_0]
                          · linarith only [h95, h96, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h124 | h124
                          · linarith only [h0, h124, h28, h95, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h124, h2, h89, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h127 | h127
      · rcases m.htr 0 2 4 (by decide) (by decide) with h128 | h128
        · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
          · linarith only [h0, h1, h129, hlam]
          · linarith only [h127, h129, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
        · linarith only [h127, h128, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h133 | h133
        · rcases m.htr 0 2 5 (by decide) (by decide) with h134 | h134
          · linarith only [h127, h134, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h136 | h136
            · linarith only [h127, h136, hc02, hlam, hphi, u2elo1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
              · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
                · linarith only [h0, h1, h134, h139, hlam]
                · linarith only [h0, h1, h138, h139, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · linarith only [h127, h133, h138, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h143 | h143
          · linarith only [h127, h143, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h145 | h145
            · linarith only [h0, h1, h127, h145, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h147 | h147
              · linarith only [h0, h133, h147, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h149 | h149
                · linarith only [h0, h127, h143, h149, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi0]
                · linarith only [h0, h1, h149, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
    · linarith only [h0, h152, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h154 | h154
      · rcases m.htr 0 2 4 (by decide) (by decide) with h155 | h155
        · rcases m.htr 0 2 5 (by decide) (by decide) with h156 | h156
          · rcases m.htr 1 2 3 (by decide) (by decide) with h157 | h157
            · rcases m.htr 1 2 4 (by decide) (by decide) with h158 | h158
              · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                    · linarith only [h0, h154, h161, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                      · linarith only [h0, h155, h161, h163, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi4]
                      · linarith only [h157, h160, h163, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                    · linarith only [h0, h154, h166, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
                      · linarith only [h0, h155, h160, h166, h168, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h170 | h170
                        · linarith only [h0, h155, h170, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h172 | h172
                          · linarith only [h166, h170, h172, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h166, h172, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h156, h159, hlam]
              · linarith only [h0, h156, h158, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
            · linarith only [h0, h156, h157, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · linarith only [h154, h156, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
        · linarith only [h154, h155, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h180 | h180
        · rcases m.htr 0 2 5 (by decide) (by decide) with h181 | h181
          · linarith only [h154, h181, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
            · linarith only [h154, h183, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h183, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h186 | h186
          · linarith only [h180, h186, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
            · linarith only [h154, h188, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h188, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_22_14_H_R_L_I (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h4bigk := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · linarith only [h4, hc23, hlam, hphi, u2ehi1]
        · linarith only [h3, hc24, hlam, hphi, u2ehi0]
      · linarith only [h0, h2, hc23, hlam, hphi, u2ehi1]
    · linarith only [h0, h1, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h10 | h10
    · rcases m.htr 0 2 3 (by decide) (by decide) with h11 | h11
      · rcases m.htr 0 2 4 (by decide) (by decide) with h12 | h12
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
          · rcases m.htr 1 2 4 (by decide) (by decide) with h14 | h14
            · linarith only [h0, h10, h14, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
            · linarith only [h14, hc24, hlam, hphi, u2ehi1]
          · linarith only [h0, h10, h11, h12, h13, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
        · linarith only [h12, hc24, hlam, hphi, u2ehi0]
      · linarith only [h11, hc23, hlam, hphi, u2ehi0]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h20 | h20
      · rcases m.htr 0 2 4 (by decide) (by decide) with h21 | h21
        · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
          · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
            · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
              · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                    · rcases h4bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h10, hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h26, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi4]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        rcases p28_3 (m.d 0 4) (by simp) with h32 | h32
                        · rcases p28_3 (m.d 1 4) (by simp) with h33 | h33
                          · rcases p28_3 (m.d 2 4) (by simp) with h34 | h34
                            · linarith only [h21, h34, hlam]
                            · linarith only [h25, h34, hlam]
                          · linarith only [h24, h33, hlam]
                        · linarith only [h32, hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        rcases p28_3 (m.d 0 4) (by simp) with h39 | h39
                        · rcases p28_3 (m.d 1 4) (by simp) with h40 | h40
                          · rcases p28_3 (m.d 2 4) (by simp) with h41 | h41
                            · linarith only [h21, h41, hlam]
                            · linarith only [h26, h41, hlam]
                          · linarith only [h10, h21, h26, h27, h40, hc34, hlam, hphi, ht23, u2ehi4]
                        · linarith only [h39, hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h21, h24, h26, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi4]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h22, h24, h26, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi4]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        rcases p28_3 (m.d 0 4) (by simp) with h49 | h49
                        · linarith only [h10, h49, hlam]
                        · linarith only [h20, h21, h25, h26, h49, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        rcases p28_3 (m.d 0 4) (by simp) with h52 | h52
                        · linarith only [h10, h52, hlam]
                        · linarith only [h0, h20, h21, h25, h26, h27, h52, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h21, hlam, p28_1]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h23, hlam, p28_1]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h0, h21, h27, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p28_1]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        rcases p28_3 (m.d 0 4) (by simp) with h59 | h59
                        · rcases p28_3 (m.d 1 4) (by simp) with h60 | h60
                          · rcases p28_3 (m.d 2 4) (by simp) with h61 | h61
                            · rcases p28_3 (m.d 3 4) (by simp) with h62 | h62
                              · linarith only [h25, h62, hlam]
                              · linarith only [h27, h62, hlam]
                            · linarith only [h61, hlam, p28_0]
                          · linarith only [h10, h21, h27, h60, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h21, h59, hlam, p28_1]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h0, h20, h21, h25, h26, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi4]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h24, hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h25, hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h0, h20, h25, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p28_1]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h21, h26, hc45, hlam, hphi, ht23, ht34, p28_1, u2ehi4]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h0, h10, h20, h21, h25, h26, h27, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p28_1, u2ehi4]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h26, hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [h27, hlam, p28_0]
                      · have p28_0 := h28c.1
                        have p28_1 := h28c.2.1
                        have p28_2 := h28c.2.2.1
                        have p28_3 := h28c.2.2.2
                        linarith only [hlam, p28_0]
                    · rcases h4bigk with h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c | h78c
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h10, hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h26, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p78_1, u2ehi4]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        rcases p78_3 (m.d 0 4) (by simp) with h82 | h82
                        · rcases p78_3 (m.d 1 4) (by simp) with h83 | h83
                          · rcases p78_3 (m.d 2 4) (by simp) with h84 | h84
                            · linarith only [h21, h84, hlam]
                            · linarith only [h25, h84, hlam]
                          · linarith only [h24, h83, hlam]
                        · linarith only [h82, hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        rcases p78_3 (m.d 0 4) (by simp) with h89 | h89
                        · rcases p78_3 (m.d 1 4) (by simp) with h90 | h90
                          · rcases p78_3 (m.d 2 4) (by simp) with h91 | h91
                            · linarith only [h21, h91, hlam]
                            · linarith only [h26, h91, hlam]
                          · linarith only [h10, h90, hlam, p78_1]
                        · linarith only [h89, hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h21, h26, h27, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p78_1]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h23, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p78_1, u2ehi3]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        rcases p78_3 (m.d 0 4) (by simp) with h99 | h99
                        · linarith only [h10, h99, hlam]
                        · linarith only [h21, h26, h27, h99, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        rcases p78_3 (m.d 0 4) (by simp) with h102 | h102
                        · linarith only [h10, h102, hlam]
                        · linarith only [h102, h21, h26, hlam]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h21, hlam, p78_1]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h23, hlam, p78_1]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        rcases p78_3 (m.d 0 4) (by simp) with h108 | h108
                        · rcases p78_3 (m.d 1 4) (by simp) with h109 | h109
                          · rcases p78_3 (m.d 2 4) (by simp) with h110 | h110
                            · rcases p78_3 (m.d 3 4) (by simp) with h111 | h111
                              · linarith only [h111, h25, hlam]
                              · rcases p78_3 (m.d 4 5) (by simp) with h113 | h113
                                · linarith only [h113, h26, hlam]
                                · linarith only [h113, h27, hlam]
                            · linarith only [h110, h25, hlam]
                          · linarith only [h109, h24, hlam]
                        · linarith only [h108, h21, h26, h27, hlam]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h20, h25, h27, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p78_1]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h21, h26, hc34, hlam, hphi, ht23, p78_1, u2ehi4]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h24, hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h25, hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h27, hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h21, h26, hlam, p78_1]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h0, h20, h25, h26, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p78_1]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h26, hlam, p78_0]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [h0, h20, h25, h26, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p78_1]
                      · have p78_0 := h78c.1
                        have p78_1 := h78c.2.1
                        have p78_2 := h78c.2.2.1
                        have p78_3 := h78c.2.2.2
                        linarith only [hlam, p78_0]
                  · linarith only [h26, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                · linarith only [h25, hc34, hlam, hphi, ht23, u2ehi2]
              · linarith only [h22, h24, hc34, hlam, hphi, ht23, u2ehi2]
            · linarith only [h0, h20, h21, h23, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
          · linarith only [h0, h20, h22, hlam]
        · linarith only [h20, h21, hc24, hlam, hphi, u2ehi2]
      · linarith only [h20, hc23, hlam, hphi, u2ehi0]

end R2N4
