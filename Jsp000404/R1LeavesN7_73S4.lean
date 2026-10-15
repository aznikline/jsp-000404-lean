import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_I_L_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have h4ehi := hb4.1
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                · linarith only [h0, h11, h14, h16, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                                  · linarith only [h0, h11, h14, h18, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h0, h11, h13, h18, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                              · linarith only [h0, h21, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                                · linarith only [h0, h11, h13, h21, h23, h4, h6, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h25 | h25
                                  · linarith only [h13, h25, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                                    · linarith only [h11, h13, h27, hlam]
                                    · rcases h0bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h13, h4, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi3]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h13, h6, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi3]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h13, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi3]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi4]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h0, hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h13, h6, h8, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi3]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h0, h13, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi3]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h0, h13, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi3]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h1, hlam, p29_1]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h4, hlam, p29_1]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h13, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi3]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h0, h13, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi3]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h2, hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h5, hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h6, hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h13, h8, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p29_1, u1ehi3]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h3, hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h4, h6, hc05, hlam, hphi, ht0b, ht45, ht5b, p29_1, u4ehi0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h7, hlam, p29_0]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [h8, hlam, p29_1]
                                      · have p29_0 := h29c.1
                                        have p29_1 := h29c.2.1
                                        have p29_2 := h29c.2.2.1
                                        have p29_3 := h29c.2.2.2
                                        linarith only [hlam, p29_0]
                          · linarith only [h0, h11, h12, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h56 | h56
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                              · linarith only [h11, h58, h9, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h61 | h61
                                  · linarith only [h0, h10, h61, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h2, h57, h61, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · linarith only [h11, h56, h60, hc23, hc34, hlam, hphi]
                            · linarith only [h11, h56, h57, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h66 | h66
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h67 | h67
                              · linarith only [h0, h67, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h69 | h69
                                · linarith only [h56, h69, h9, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h71 | h71
                                  · linarith only [h0, h10, h71, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h2, h66, h71, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                              · linarith only [h11, h74, h9, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                                · linarith only [h56, h76, hc23, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                                  · linarith only [h10, h66, h78, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h80 | h80
                                    · linarith only [h66, h80, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                                    · linarith only [h0, h11, h4, h6, h8, h80, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
                        · linarith only [h0, h10, h5, h83, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                              · linarith only [h0, h10, h5, h83, h87, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                                · linarith only [h0, h10, h4, h6, h87, h89, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h10, h4, h6, h85, h87, h89, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h10, h85, h86, h9, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                              · linarith only [h0, h83, h9, h94, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h96 | h96
                                · linarith only [h10, h4, h6, h85, h9, h94, h96, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
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
                                        linarith only [h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, p100_1, u4ehi0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h10, h6, h94, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi1]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p100_1, u4ehi0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h3, h85, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi2]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h0, hlam, p100_0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [hlam, p100_0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h10, h6, h94, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi1]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h0, h2, h93, hc01, hlam, hphi, ht0b, ht45, ht5b, p100_1, u4ehi4]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h0, h7, h85, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi2]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h1, hlam, p100_1]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h4, hlam, p100_1]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [hlam, p100_0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h10, h6, h9, h94, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi2]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h0, h4, h7, h85, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi2]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h2, hlam, p100_0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h5, hlam, p100_0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h6, hlam, p100_0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [hlam, p100_0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h7, h85, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p100_1, u1ehi2]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h3, hlam, p100_0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h4, h6, hc05, hlam, hphi, ht0b, ht45, ht5b, p100_1, u4ehi0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h7, hlam, p100_0]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [h8, hlam, p100_1]
                                      · have p100_0 := h100c.1
                                        have p100_1 := h100c.2.1
                                        have p100_2 := h100c.2.2.1
                                        have p100_3 := h100c.2.2.2
                                        linarith only [hlam, p100_0]
                                    · linarith only [h10, h9, h93, h94, h99, hc14, hlam, hphi, u1ehi2]
                                  · linarith only [h10, h93, h98, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h128 | h128
                              · linarith only [h10, h128, h6, h8, h9, h93, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
                                · linarith only [h0, h10, h130, h4, h6, h8, h85, h9, h93, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h132 | h132
                                  · linarith only [h10, h128, h132, h9, h93, hc23, hc34, hlam, hphi]
                                  · linarith only [h0, h10, h132, h4, h6, h8, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h135 | h135
                      · linarith only [h0, h135, h4, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h137 | h137
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h138 | h138
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h141 | h141
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h143 | h143
                                    · linarith only [h1, h137, h143, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h139, h143, h2, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · linarith only [h135, h139, h142, hlam]
                                · linarith only [h138, h141, h9, hlam]
                              · linarith only [h0, h140, h4, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h150 | h150
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h151 | h151
                                  · linarith only [h139, h149, h151, hc23, hlam, hphi, ht12, u1ehi3]
                                  · linarith only [h135, h151, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                · linarith only [h138, h150, h9, hlam]
                              · linarith only [h0, h149, h4, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                          · linarith only [h0, h137, h138, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                              · linarith only [h137, h159, hc23, hlam, hphi, ht12, u1ehi2]
                              · linarith only [h0, h159, h4, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                            · linarith only [h137, h157, h158, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h163 | h163
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                              · linarith only [h0, h137, h164, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                              · linarith only [h164, h9, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
                              · linarith only [h0, h137, h167, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h0, h167, h4, h6, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h171 | h171
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h173 | h173
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h174 | h174
                            · linarith only [h174, h2, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h176 | h176
                              · linarith only [h0, h170, h176, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                                · linarith only [h1, h172, h176, h178, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h180 | h180
                                  · linarith only [h180, h2, h8, hc24, hlam, hphi, ht12, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h182 | h182
                                    · linarith only [h172, h182, h2, h8, hlam]
                                    · rcases h0bigk with h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c | h184c
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi1]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi2]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi3]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h2, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi3]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h0, hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi2]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi3]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h0, h2, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi3]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h1, hlam, p184_1]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h4, hlam, p184_1]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi3]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h0, h2, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi3]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h2, hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h5, hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h6, hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h8, hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h3, hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h0, h170, h173, h176, h182, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p184_1]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h7, hlam, p184_0]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [h2, h4, h7, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p184_1, u1ehi3]
                                      · have p184_0 := h184c.1
                                        have p184_1 := h184c.2.1
                                        have p184_2 := h184c.2.2.1
                                        have p184_3 := h184c.2.2.2
                                        linarith only [hlam, p184_0]
                          · linarith only [h0, h172, h173, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h172, h6, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h171, h5, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
                      · linarith only [h0, h170, h213, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h213, h5, h8, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                  · linarith only [h216, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h220 | h220
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h221 | h221
                          · linarith only [h1, h221, h7, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h223 | h223
                            · linarith only [h2, h216, h223, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h225 | h225
                              · linarith only [h0, h218, h225, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · linarith only [h1, h220, h225, h7, hc23, hc35, hlam, hphi]
                        · linarith only [h220, h6, h7, hc13, hc35, hlam, hphi]
                      · linarith only [h216, h219, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h218, h4, h7, hc35, hlam, hphi, ht12, ht23, u1ehi1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h231 | h231
                · rcases m.htr 0 4 5 (by decide) (by decide) with h232 | h232
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h233 | h233
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h235 | h235
                        · linarith only [h231, h235, h3, h6, hc13, hlam, hphi, u1ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                              · linarith only [h231, h233, h239, h3, h6, hc12, hlam, hphi, u1ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h241 | h241
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h242 | h242
                                  · linarith only [h0, h234, h242, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h2, h238, h242, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                · linarith only [h231, h241, h6, hc23, hc34, hlam, hphi]
                            · linarith only [h232, h238, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h231, h237, h6, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h248 | h248
                        · linarith only [h0, h233, h234, h248, h5, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h250 | h250
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h251 | h251
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h252 | h252
                              · linarith only [h233, h234, h250, h252, h5, h6, hc23, hlam, hphi, ht12, u1ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h254 | h254
                                · linarith only [h0, h233, h234, h254, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h231, h254, h6, hc23, hc34, hlam, hphi]
                            · linarith only [h232, h251, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h231, h250, h6, hc13, hc34, hlam, hphi]
                    · linarith only [h233, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h231, h232, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h261 | h261
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h262 | h262
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                        · linarith only [h1, h264, h6, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h266 | h266
                          · linarith only [h1, h231, h266, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h268 | h268
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                              · linarith only [h1, h262, h269, h6, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h271 | h271
                                · linarith only [h1, h231, h262, h271, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h273 | h273
                                  · linarith only [h0, h263, h273, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h2, h268, h273, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                            · linarith only [h261, h268, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
                        · linarith only [h1, h261, h277, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                          · linarith only [h0, h231, h262, h263, h279, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
                              · linarith only [h0, h262, h263, h282, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h284 | h284
                                · linarith only [h0, h231, h262, h263, h284, h5, hc01, hc05, hlam, hphi, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h286 | h286
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h287 | h287
                                    · rcases h0bigk with h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c | h288c
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [hlam, p288_0]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h263, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p288_1]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p288_1, u1ehi2]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht0b, ht45, ht5b, p288_1, u4ehi0]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h1, h231, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p288_1, u1ehi2]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h0, hlam, p288_0]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [hlam, p288_0]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p288_1, u1ehi2]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h0, h2, h281, hc01, hlam, hphi, ht0b, ht45, ht5b, p288_1, u4ehi4]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h0, h1, h231, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p288_1, u1ehi2]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h1, hlam, p288_1]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h4, hlam, p288_1]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [hlam, p288_0]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h6, hlam, p288_1]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h231, hlam, p288_1]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h2, hlam, p288_0]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h5, hlam, p288_0]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p288_1, u1ehi2]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [hlam, p288_0]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h1, h231, h6, hc34, hlam, hphi, ht12, ht23, p288_1, u1ehi2]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h3, hlam, p288_0]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h0, h262, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p288_1, u1ehi2]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h1, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p288_1, u1ehi2]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [h261, hlam, p288_1]
                                      · have p288_0 := h288c.1
                                        have p288_1 := h288c.2.1
                                        have p288_2 := h288c.2.2.1
                                        have p288_3 := h288c.2.2.2
                                        linarith only [hlam, p288_0]
                                    · linarith only [h2, h281, h287, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                                  · linarith only [h262, h263, h281, h286, hc14, hlam, hphi, u1ehi2]
                            · linarith only [h261, h281, h6, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · linarith only [h262, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h320 | h320
                        · linarith only [h1, h261, h320, h6, hc45, hlam, hphi, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
                          · linarith only [h1, h231, h322, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h324 | h324
                            · linarith only [h2, h261, h324, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                              · linarith only [h1, h318, h326, h6, hc12, hlam, hphi, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h328 | h328
                                · linarith only [h1, h231, h328, hc23, hlam, hphi, ht12, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h330 | h330
                                  · linarith only [h0, h261, h319, h330, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h332 | h332
                                    · linarith only [h1, h261, h332, h6, hc34, hlam, hphi, ht12, ht23, u1ehi2]
                                    · linarith only [h1, h332, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h261, h319, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h318, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h337 | h337
              · linarith only [h337, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h339 | h339
                · rcases m.htr 0 4 5 (by decide) (by decide) with h340 | h340
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h341 | h341
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                      · linarith only [h0, h339, h342, h4, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                        · linarith only [h3, h337, h339, h344, hc13, hlam, hphi, u1ehi4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
                              · linarith only [h0, h3, h337, h339, h341, h348, h5, hc24, hlam, hphi, ht12, u1ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h350 | h350
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h351 | h351
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h352 | h352
                                    · linarith only [h0, h341, h348, h350, h352, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                                    · linarith only [h0, h341, h348, h352, h5, hc23, hc45, hlam, hphi, ht34]
                                  · linarith only [h0, h2, h341, h347, h350, h351, h5, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h339, h348, h350, h4, h5, hc23, hc34, hlam, hphi]
                            · linarith only [h337, h340, h347, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                          · linarith only [h339, h346, h4, h5, hc24, hlam, hphi, ht12, u1ehi2]
                    · linarith only [h341, h4, h5, hc24, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h339, h340, h4, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h361 | h361
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h363 | h363
                      · linarith only [h0, h363, h5, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h365 | h365
                        · linarith only [h1, h337, h365, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h367 | h367
                          · linarith only [h1, h339, h367, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
                              · linarith only [h1, h337, h370, hc23, hlam, hphi, ht12, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h372 | h372
                                · linarith only [h1, h339, h362, h372, hc12, hlam, hphi, u1ehi2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h374 | h374
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h375 | h375
                                    · rcases h0bigk with h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c | h376c
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p376_1, u1ehi2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p376_1, u1ehi2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h2, h369, hc01, hlam, hphi, ht0b, ht45, ht5b, p376_1, u4ehi4]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, h339, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p376_1, u1ehi2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p376_1, u1ehi2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h5, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, h339, h370, h5, hc34, hlam, hphi, ht12, ht23, p376_1, u1ehi2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h4, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h337, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h339, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h2, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h0, h362, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, h370, h5, hc34, hlam, hphi, ht12, ht23, p376_1, u1ehi2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, h339, h370, h5, hc34, hlam, hphi, ht12, ht23, p376_1, u1ehi2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h3, hlam, p376_0]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, h4, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p376_1, u1ehi2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h1, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p376_1, u1ehi2]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [h361, hlam, p376_1]
                                      · have p376_0 := h376c.1
                                        have p376_1 := h376c.2.1
                                        have p376_2 := h376c.2.2.1
                                        have p376_3 := h376c.2.2.2
                                        linarith only [hlam, p376_0]
                                    · linarith only [h2, h369, h370, h375, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                                  · linarith only [h1, h2, h369, h374, h4, h5, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi2]
                            · linarith only [h337, h361, h369, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                    · linarith only [h362, h4, h5, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h407 | h407
                      · linarith only [h0, h361, h407, h5, hc45, hlam, hphi, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h409 | h409
                        · linarith only [h1, h361, h4, h409, h5, hc45, hlam, hphi, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
                          · linarith only [h1, h339, h411, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h413 | h413
                            · linarith only [h0, h361, h413, h5, hc14, hlam, hphi, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h415 | h415
                              · linarith only [h1, h337, h406, h415, hc12, hlam, hphi, u1ehi2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h417 | h417
                                · linarith only [h0, h3, h339, h406, h413, h415, h417, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h419 | h419
                                  · linarith only [h1, h361, h4, h419, h5, hc24, hlam, hphi, ht12, u1ehi2]
                                  · linarith only [h1, h4, h419, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h4, h406, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h423 | h423
            · rcases m.htr 0 3 4 (by decide) (by decide) with h424 | h424
              · rcases m.htr 0 3 5 (by decide) (by decide) with h425 | h425
                · rcases m.htr 0 4 5 (by decide) (by decide) with h426 | h426
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h427 | h427
                    · linarith only [h4, h423, h427, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h429 | h429
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h430 | h430
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h431 | h431
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h432 | h432
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h433 | h433
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h434 | h434
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h435 | h435
                                  · linarith only [h0, h4, h429, h435, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                  · linarith only [h2, h432, h433, h435, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h4, h423, h431, h434, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                              · linarith only [h2, h4, h423, h432, h433, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                            · linarith only [h4, h423, h426, h432, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                          · linarith only [h4, h425, h431, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h424, h427, h429, h430, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h4, h423, h429, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
                    · linarith only [h4, h423, h444, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h446 | h446
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h449 | h449
                            · linarith only [h2, h426, h449, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h451 | h451
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h452 | h452
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h453 | h453
                                  · linarith only [h0, h2, h426, h446, h453, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h455 | h455
                                    · linarith only [h0, h2, h4, h426, h446, h451, h455, hc23, hlam, hphi, ht12, u1ehi3]
                                    · rcases h0bigk with h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c | h457c
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h0, h446, h451, hc01, hlam, hphi, ht0b, ht45, ht5b, p457_1, u4ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h1, h448, hc01, hc35, hlam, hphi, ht0b, ht5b, p457_1]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h0, h2, h4, h446, h451, hc01, hc23, hlam, hphi, ht0b, ht12, ht45, ht5b, p457_1, u1ehi3, u4ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h0, h3, h4, h446, h451, hc01, hc23, hlam, hphi, ht0b, ht12, ht45, ht5b, p457_1, u1ehi4, u4ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h0, hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h4, hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h2, h4, hc23, hlam, hphi, ht12, p457_1, u1ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h2, h4, h426, hc23, hlam, hphi, ht12, p457_1, u1ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h1, hlam, p457_1]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h0, h446, h451, hc03, hlam, hphi, ht0b, ht45, ht5b, p457_1, u4ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h2, h4, hc23, hlam, hphi, ht12, p457_1, u1ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h2, h4, h426, hc23, hlam, hphi, ht12, p457_1, u1ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h2, hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h423, hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h424, hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h426, hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h3, hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h0, h446, h451, hc05, hlam, hphi, ht0b, ht45, ht5b, p457_1, u4ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h425, hlam, p457_0]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [h0, h2, h4, h446, h451, hc05, hc23, hlam, hphi, ht0b, ht12, ht45, ht5b, p457_1, u1ehi3, u4ehi3]
                                      · have p457_0 := h457c.1
                                        have p457_1 := h457c.2.1
                                        have p457_2 := h457c.2.2.1
                                        have p457_3 := h457c.2.2.2
                                        linarith only [hlam, p457_0]
                                · linarith only [h0, h4, h446, h451, h452, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h4, h446, h451, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                          · linarith only [h4, h425, h448, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h4, h424, h444, h446, h447, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h4, h423, h446, hc23, hlam, hphi, ht12, u1ehi1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
                  · linarith only [h4, h423, h425, h488, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
                    · linarith only [h0, h4, h423, h490, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h493 | h493
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h494 | h494
                          · linarith only [h1, h425, h494, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h496 | h496
                            · linarith only [h2, h488, h496, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h498 | h498
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h499 | h499
                                · linarith only [h1, h425, h490, h492, h498, h499, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                · linarith only [h0, h4, h492, h498, h499, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                              · linarith only [h0, h4, h492, h498, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h424, h425, h493, hc13, hc35, hlam, hphi]
                      · linarith only [h4, h423, h492, hc23, hlam, hphi, ht12, u1ehi1]
              · linarith only [h4, h423, h424, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h506 | h506
              · rcases m.htr 0 3 5 (by decide) (by decide) with h507 | h507
                · rcases m.htr 0 4 5 (by decide) (by decide) with h508 | h508
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h509 | h509
                    · linarith only [h0, h1, h4, h423, h509, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h511 | h511
                      · linarith only [h0, h423, h511, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h513 | h513
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h514 | h514
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h515 | h515
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h516 | h516
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h517 | h517
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h518 | h518
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h519 | h519
                                    · linarith only [h1, h513, h519, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h2, h515, h519, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                  · linarith only [h1, h423, h513, h515, h518, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                · linarith only [h2, h3, h4, h506, h514, h515, h517, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h4, h516, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h4, h506, h508, h515, hc23, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h4, h507, h514, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h4, h506, h509, h513, hc23, hlam, hphi, ht12, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h528 | h528
                    · linarith only [h0, h1, h4, h423, h528, hc24, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h530 | h530
                      · linarith only [h0, h423, h508, h530, hc45, hlam, hphi, u4ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h532 | h532
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h533 | h533
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h534 | h534
                            · linarith only [h0, h423, h508, h534, hc14, hlam, hphi, u1ehi1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h536 | h536
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h537 | h537
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h538 | h538
                                  · linarith only [h0, h423, h508, h536, h538, hc23, hlam, hphi, ht12, u1ehi1]
                                  · linarith only [h0, h423, h538, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                                · linarith only [h0, h1, h4, h533, h537, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                              · linarith only [h0, h4, h536, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                          · linarith only [h507, h532, h533, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h4, h506, h532, hc23, hlam, hphi, ht12, u1ehi2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h545 | h545
                  · linarith only [h506, h507, h545, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h547 | h547
                    · linarith only [h0, h4, h547, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h549 | h549
                      · linarith only [h0, h423, h549, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h551 | h551
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h552 | h552
                          · linarith only [h1, h507, h552, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h554 | h554
                            · linarith only [h2, h545, h554, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h556 | h556
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h557 | h557
                                · linarith only [h1, h507, h551, h557, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                                · linarith only [h0, h4, h557, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                              · linarith only [h0, h1, h4, h507, h551, h556, hc35, hlam, hphi, ht12, ht23, u1ehi1]
                        · linarith only [h506, h507, h551, hc13, hc35, hlam, hphi]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h562 | h562
                · rcases m.htr 0 4 5 (by decide) (by decide) with h563 | h563
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h564 | h564
                    · linarith only [h0, h4, h564, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h566 | h566
                      · linarith only [h0, h423, h566, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h568 | h568
                        · linarith only [h1, h506, h568, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h570 | h570
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h571 | h571
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h572 | h572
                              · linarith only [h1, h506, h564, h572, hc23, hlam, hphi, ht12, u1ehi1]
                              · linarith only [h0, h4, h572, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h423, h563, h571, hc24, hlam, hphi, ht12, u1ehi3]
                          · linarith only [h4, h562, h564, h570, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h506, h562, h563, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h578 | h578
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h579 | h579
                    · linarith only [h0, h4, h579, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h581 | h581
                      · linarith only [h0, h423, h581, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h583 | h583
                        · linarith only [h1, h506, h583, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h585 | h585
                          · linarith only [h0, h4, h562, h585, hc13, hlam, hphi, u1ehi1]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h587 | h587
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h588 | h588
                              · linarith only [h0, h4, h506, h588, hc23, hlam, hphi, ht12, u1ehi1]
                              · linarith only [h0, h4, h588, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                            · linarith only [h423, h578, h587, hc24, hlam, hphi, ht12, u1ehi3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h592 | h592
                    · linarith only [h0, h4, h592, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h594 | h594
                      · linarith only [h0, h423, h594, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h596 | h596
                        · linarith only [h1, h506, h578, h596, hc45, hlam, hphi, u4ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h598 | h598
                          · linarith only [h1, h3, h506, h562, h578, h598, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h600 | h600
                            · linarith only [h2, h578, h600, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h602 | h602
                              · linarith only [h0, h4, h506, h602, hc23, hlam, hphi, ht12, u1ehi1]
                              · linarith only [h0, h4, h602, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h608 | h608
    · linarith only [h0, h608, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h610 | h610
      · linarith only [h0, h610, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h612 | h612
        · linarith only [h0, h612, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h614 | h614
          · rcases m.htr 0 2 4 (by decide) (by decide) with h615 | h615
            · rcases m.htr 0 3 4 (by decide) (by decide) with h616 | h616
              · rcases m.htr 0 3 5 (by decide) (by decide) with h617 | h617
                · rcases m.htr 0 4 5 (by decide) (by decide) with h618 | h618
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h619 | h619
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h620 | h620
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h621 | h621
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h622 | h622
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h623 | h623
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h625 | h625
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h626 | h626
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h627 | h627
                                    · linarith only [h614, h624, h627, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h0, h615, h626, h627, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h630 | h630
                                    · linarith only [h624, h626, h630, hlam]
                                    · rcases h0bigk with h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c | h632c
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [hlam, p632_0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h0, hlam, p632_1]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h608, hlam, p632_0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h610, hlam, p632_1]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h612, hlam, p632_1]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, p632_1, u1ehi0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [hlam, p632_0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h0, h616, h618, h624, h626, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p632_1, u4ehi3]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h0, h618, h624, h626, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p632_1, u4ehi3]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h0, h612, hc12, hlam, hphi, p632_1, u1ehi0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u1ehi0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h614, hlam, p632_1]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [hlam, p632_0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h608, h618, h619, h624, h626, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p632_1, u4ehi3]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h608, h612, h619, hc12, hlam, hphi, p632_1, u1ehi0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p632_1, u1ehi0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h615, hlam, p632_0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h616, hlam, p632_0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [hlam, p632_0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h610, h612, h619, h621, hc12, hlam, hphi, p632_1, u1ehi0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h610, h618, h619, h621, h624, h626, hc05, hc12, hlam, hphi, ht0b, ht45, ht5b, p632_1, u1ehi0, u4ehi3]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h612, h614, h619, h621, h623, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p632_1]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h617, hlam, p632_0]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [h618, hlam, p632_1]
                                      · have p632_0 := h632c.1
                                        have p632_1 := h632c.2.1
                                        have p632_2 := h632c.2.2.1
                                        have p632_3 := h632c.2.2.2
                                        linarith only [hlam, p632_0]
                                · linarith only [h608, h617, h619, h624, h625, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h659 | h659
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h660 | h660
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h661 | h661
                                    · linarith only [h608, h616, h619, h624, h659, h661, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                                    · linarith only [h624, h659, h660, h661, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h624, h659, h660, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h665 | h665
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h666 | h666
                                    · rcases h0bigk with h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c | h667c
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [hlam, p667_0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h0, hlam, p667_1]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h608, hlam, p667_0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h610, hlam, p667_1]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h612, hlam, p667_1]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, p667_1, u1ehi0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [hlam, p667_0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h0, h616, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p667_1, u4ehi3]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p667_1, u4ehi0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h0, h617, h659, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p667_1]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p667_1, u1ehi0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h614, hlam, p667_1]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [hlam, p667_0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h608, h615, h619, h665, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p667_1, u4ehi4]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h608, h612, h619, hc12, hlam, hphi, p667_1, u1ehi0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p667_1, u1ehi0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h615, hlam, p667_0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h616, hlam, p667_0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [hlam, p667_0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h610, h612, h619, h621, hc12, hlam, hphi, p667_1, u1ehi0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p667_1, u1ehi0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h0, h612, h619, h621, h623, hc12, hlam, hphi, p667_1, u1ehi0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h617, hlam, p667_0]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [h618, hlam, p667_1]
                                      · have p667_0 := h667c.1
                                        have p667_1 := h667c.2.1
                                        have p667_2 := h667c.2.2.1
                                        have p667_3 := h667c.2.2.2
                                        linarith only [hlam, p667_0]
                                    · linarith only [h624, h665, h666, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
                                    · linarith only [h608, h616, h619, h665, h694, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                    · rcases h0bigk with h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [hlam, p696_0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h0, hlam, p696_1]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h608, hlam, p696_0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h610, hlam, p696_1]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h612, hlam, p696_1]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h610, h618, h619, h621, h624, h694, hc02, hc12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p696_1, u1ehi0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [hlam, p696_0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h0, h608, hc12, hlam, hphi, p696_1, u1ehi0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h0, h618, h624, h694, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p696_1]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h0, h612, hc12, hlam, hphi, p696_1, u1ehi0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p696_1, u1ehi0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h614, hlam, p696_1]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [hlam, p696_0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h0, h614, h618, h624, h694, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p696_1]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h0, h612, h614, hc12, hlam, hphi, p696_1, u1ehi0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p696_1, u1ehi0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h615, hlam, p696_0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h616, hlam, p696_0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [hlam, p696_0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h0, h612, h614, h616, hc12, hlam, hphi, p696_1, u1ehi0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h0, h614, h616, h618, h624, h694, hc05, hc12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p696_1, u1ehi0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h614, h616, h618, hlam, p696_1]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h617, hlam, p696_0]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [h618, hlam, p696_1]
                                      · have p696_0 := h696c.1
                                        have p696_1 := h696c.2.1
                                        have p696_2 := h696c.2.2.1
                                        have p696_3 := h696c.2.2.2
                                        linarith only [hlam, p696_0]
                            · linarith only [h0, h614, h616, h618, h623, hc12, hlam, hphi, u1ehi3]
                          · linarith only [h608, h622, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h608, h621, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h608, h619, h620, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h619, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h727 | h727
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h728 | h728
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h729 | h729
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h730 | h730
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h731 | h731
                            · linarith only [h610, h618, h727, h729, h731, hc12, hlam, hphi, u1ehi0]
                            · linarith only [h610, h731, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                          · linarith only [h0, h614, h617, h730, hc12, hlam, hphi, u1ehi2]
                        · linarith only [h608, h729, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h728, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h614, h727, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h738 | h738
                  · linarith only [h616, h617, h738, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h740 | h740
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h741 | h741
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h742 | h742
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h743 | h743
                          · linarith only [h616, h617, h740, h743, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h608, h743, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                        · linarith only [h608, h616, h742, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                      · linarith only [h615, h738, h741, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h0, h614, h740, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h749 | h749
                · rcases m.htr 0 4 5 (by decide) (by decide) with h750 | h750
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h751 | h751
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h753 | h753
                        · linarith only [h608, h616, h751, h753, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h608, h753, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h752, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h614, h751, hlam]
                  · linarith only [h616, h749, h750, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h759 | h759
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h760 | h760
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h761 | h761
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h762 | h762
                        · linarith only [h608, h616, h760, h762, hc12, hlam, hphi, u1ehi0]
                        · linarith only [h608, h762, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h0, h761, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h614, h760, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h767 | h767
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h768 | h768
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h769 | h769
                        · linarith only [h608, h616, h769, hc13, hlam, hphi, u1ehi0]
                        · linarith only [h608, h769, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                      · linarith only [h615, h759, h768, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi1]
                    · linarith only [h0, h614, h767, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h774 | h774
              · linarith only [h614, h615, h774, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h776 | h776
                · rcases m.htr 0 4 5 (by decide) (by decide) with h777 | h777
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h778 | h778
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h779 | h779
                      · linarith only [h0, h615, h779, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h779, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h778, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h614, h615, h776, h777, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h784 | h784
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h785 | h785
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h786 | h786
                      · linarith only [h0, h615, h786, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h786, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h614, h785, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h790 | h790
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h791 | h791
                      · linarith only [h0, h615, h791, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h0, h791, hc24, hlam, hphi, ht12, u1ehi0]
                    · linarith only [h0, h614, h790, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h795 | h795
            · rcases m.htr 0 3 4 (by decide) (by decide) with h796 | h796
              · rcases m.htr 0 3 5 (by decide) (by decide) with h797 | h797
                · rcases m.htr 0 4 5 (by decide) (by decide) with h798 | h798
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h799 | h799
                    · linarith only [h614, h795, h799, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h799, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                    · linarith only [h0, h614, h802, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h802, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h805 | h805
                  · linarith only [h614, h795, h797, h805, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h807 | h807
                    · linarith only [h0, h614, h807, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h807, hc23, hlam, hphi, ht12, u1ehi0]
              · linarith only [h614, h795, h796, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h811 | h811
              · rcases m.htr 0 3 5 (by decide) (by decide) with h812 | h812
                · rcases m.htr 0 4 5 (by decide) (by decide) with h813 | h813
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h814 | h814
                    · linarith only [h0, h614, h814, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h814, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h817 | h817
                    · linarith only [h0, h614, h817, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h817, hc23, hlam, hphi, ht12, u1ehi0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h820 | h820
                  · linarith only [h811, h812, h820, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h822 | h822
                    · linarith only [h0, h614, h822, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h822, hc23, hlam, hphi, ht12, u1ehi0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h825 | h825
                · rcases m.htr 0 4 5 (by decide) (by decide) with h826 | h826
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h827 | h827
                    · linarith only [h0, h614, h827, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h827, hc23, hlam, hphi, ht12, u1ehi0]
                  · linarith only [h811, h825, h826, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h831 | h831
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h832 | h832
                    · linarith only [h0, h614, h832, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h832, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h835 | h835
                    · linarith only [h0, h614, h835, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h835, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
