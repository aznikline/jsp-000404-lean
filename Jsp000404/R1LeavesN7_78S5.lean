import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_12_24_L_0_M_LI (m : N7Model)
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h10, h12, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · linarith only [h12, h5, hc34, hlam, hphi, u4elo0]
                        · linarith only [h11, h2, h9, hc24, hlam, hphi, u4elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                          · rcases h4bigk with h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c | h18c
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hc14, hlam, hphi, p18_1, u4elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h0, h10, h16, h6, h8, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p18_1, u2elo0, u4elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h10, hc23, hlam, hphi, ht34, p18_1, u4elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              rcases p18_3 (m.d 0 4) (by simp) with h23 | h23
                              · rcases p18_3 (m.d 1 4) (by simp) with h24 | h24
                                · linarith only [h2, h24, hlam]
                                · linarith only [h24, h9, hlam]
                              · linarith only [h23, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h2, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h0, h10, h16, h6, h8, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p18_1, u2elo0, u4elo1]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h10, h2, hc23, hlam, hphi, ht34, p18_1, u4elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              rcases p18_3 (m.d 0 4) (by simp) with h32 | h32
                              · rcases p18_3 (m.d 1 4) (by simp) with h33 | h33
                                · rcases p18_3 (m.d 2 4) (by simp) with h34 | h34
                                  · linarith only [h34, h7, hlam]
                                  · linarith only [h16, h34, hlam]
                                · linarith only [h33, hlam, p18_0]
                              · linarith only [h32, h5, hlam]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h3, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h7, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h10, hlam, p18_1]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18_1, u2elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h4, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h8, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h0, h6, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p18_1, u2elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h0, h6, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18_1, u2elo0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h5, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h9, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h16, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [h17, hlam, p18_0]
                            · have p18_0 := h18c.1
                              have p18_1 := h18c.2.1
                              have p18_2 := h18c.2.2.1
                              have p18_3 := h18c.2.2.2
                              linarith only [hlam, p18_0]
                          · linarith only [h16, h17, hc34, hlam, hphi, u4elo2]
                        · linarith only [h16, h2, h9, hc24, hlam, hphi, u4elo0]
                    · linarith only [h5, h9, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                      · linarith only [h58, h6, h8, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h61 | h61
                          · rcases h4bigk with h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c | h62c
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h60, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p62_1, u4elo0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h60, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p62_1, u4elo0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h8, hc13, hlam, hphi, ht34, p62_1, u4elo0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              rcases p62_3 (m.d 0 4) (by simp) with h67 | h67
                              · rcases p62_3 (m.d 1 4) (by simp) with h68 | h68
                                · linarith only [h2, h68, hlam]
                                · linarith only [h57, h68, hlam]
                              · linarith only [h67, hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h2, hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h60, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p62_1, u4elo1]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h8, hlam, p62_1]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              rcases p62_3 (m.d 0 4) (by simp) with h76 | h76
                              · rcases p62_3 (m.d 1 4) (by simp) with h77 | h77
                                · rcases p62_3 (m.d 2 4) (by simp) with h78 | h78
                                  · linarith only [h7, h78, hlam]
                                  · linarith only [h60, h78, hlam]
                                · linarith only [h77, hlam, p62_0]
                              · linarith only [h5, h76, hlam]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h3, hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h7, hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h58, hlam, p62_1]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p62_1, u2elo0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h4, hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [hc14, hlam, hphi, p62_1, u4elo3]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h4, hc24, hlam, hphi, p62_1, u4elo0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              rcases p62_3 (m.d 0 4) (by simp) with h92 | h92
                              · rcases p62_3 (m.d 1 4) (by simp) with h93 | h93
                                · linarith only [h8, h93, hlam]
                                · linarith only [h57, h93, hlam]
                              · linarith only [h5, h92, hlam]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h5, hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h57, hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h60, hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [h61, hlam, p62_0]
                            · have p62_0 := h62c.1
                              have p62_1 := h62c.2.1
                              have p62_2 := h62c.2.2.1
                              have p62_3 := h62c.2.2.2
                              linarith only [hlam, p62_0]
                          · linarith only [h60, h61, h7, hc34, hlam, hphi, u4elo1]
                        · linarith only [h4, h57, h60, h8, hc24, hlam, hphi, u4elo0]
                    · linarith only [h5, h57, hc14, hlam, hphi, u4elo0]
                · linarith only [h3, h7, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h110 | h110
                        · linarith only [h106, h110, h6, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                        · linarith only [h108, h110, hc24, hlam, hphi, u4elo1]
                      · linarith only [h109, h6, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h108, h5, hc14, hlam, hphi, u4elo0]
                  · linarith only [h106, h107, h6, hc24, hlam, hphi, u4elo3]
                · linarith only [h106, h3, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
              · rcases m.htr 1 2 4 (by decide) (by decide) with h118 | h118
                · rcases m.htr 1 3 4 (by decide) (by decide) with h119 | h119
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h120 | h120
                    · linarith only [h120, h5, hc04, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                        · linarith only [h118, h123, h2, h5, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h125 | h125
                          · linarith only [h117, h122, h125, h5, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h4bigk with h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h118, h122, h5, hc34, hlam, hphi, p127_1, u4elo4]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h122, h5, hc34, hlam, hphi, p127_1, u4elo4]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h5, hc34, hlam, hphi, p127_1, u4elo4]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h5, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h2, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h122, hc34, hlam, hphi, p127_1, u4elo1]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h2, h5, hc34, hlam, hphi, p127_1, u4elo4]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h120, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h3, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h118, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [hc34, hlam, hphi, p127_1, u4elo2]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h123, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h4, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h119, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h122, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h125, hlam, p127_0]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [hc04, hlam, hphi, p127_1, u4elo4]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h118, hc24, hlam, hphi, p127_1, u4elo4]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [h122, hc34, hlam, hphi, p127_1, u4elo4]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [hc34, hlam, hphi, p127_1, u4elo4]
                            · have p127_0 := h127c.1
                              have p127_1 := h127c.2.1
                              have p127_2 := h127c.2.2.1
                              have p127_3 := h127c.2.2.2
                              linarith only [hlam, p127_0]
                      · linarith only [h122, h4, h5, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h117, h119, h4, h5, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h118, h3, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                    · linarith only [h158, h2, h5, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h160 | h160
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h161 | h161
                        · linarith only [h117, h156, h161, h2, h5, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h163 | h163
                          · linarith only [h156, h160, h163, h2, h5, hlam]
                          · rcases h4bigk with h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c | h165c
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h5, hc14, hlam, hphi, p165_1, u4elo4]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h160, h5, hc34, hlam, hphi, p165_1, u4elo4]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h5, hc34, hlam, hphi, p165_1, u4elo4]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h5, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h2, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h160, hc34, hlam, hphi, p165_1, u4elo1]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h2, h5, hc34, hlam, hphi, p165_1, u4elo4]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h158, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h3, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h156, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hc34, hlam, hphi, p165_1, u4elo2]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h161, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h4, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h157, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h160, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h163, hlam, p165_0]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hc04, hlam, hphi, p165_1, u4elo4]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h156, hc24, hlam, hphi, p165_1, u4elo4]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [h160, hc34, hlam, hphi, p165_1, u4elo4]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hc34, hlam, hphi, p165_1, u4elo4]
                            · have p165_0 := h165c.1
                              have p165_1 := h165c.2.1
                              have p165_2 := h165c.2.2.1
                              have p165_3 := h165c.2.2.2
                              linarith only [hlam, p165_0]
                      · linarith only [h117, h160, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h117, h156, h157, h4, hc24, hlam, hphi, u4elo0]
                · linarith only [h156, h3, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
            · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
              · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                  · linarith only [h1, h197, h4, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h199 | h199
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                      · linarith only [h195, h200, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h202 | h202
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                          · rcases h4bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h196, h202, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p204_1, u4elo3]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h202, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p204_1, u4elo3]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h4, hlam, p204_1]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              rcases p204_3 (m.d 0 4) (by simp) with h209 | h209
                              · rcases p204_3 (m.d 1 4) (by simp) with h210 | h210
                                · linarith only [h2, h210, hlam]
                                · linarith only [h199, h210, hlam]
                              · linarith only [h209, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h2, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h202, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p204_1, u4elo1]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h197, hlam, p204_1]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              rcases p204_3 (m.d 0 4) (by simp) with h218 | h218
                              · rcases p204_3 (m.d 1 4) (by simp) with h219 | h219
                                · rcases p204_3 (m.d 2 4) (by simp) with h220 | h220
                                  · linarith only [h196, h220, hlam]
                                  · linarith only [h202, h220, hlam]
                                · linarith only [h219, hlam, p204_0]
                              · linarith only [h194, h218, hlam]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h3, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h196, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h200, hlam, p204_1]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p204_1, u2elo0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hc04, hlam, hphi, p204_1, u4elo3]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hc14, hlam, hphi, p204_1, u4elo3]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hc24, hlam, hphi, p204_1, u4elo3]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              rcases p204_3 (m.d 0 4) (by simp) with h234 | h234
                              · linarith only [h234, h4, hlam]
                              · linarith only [h194, h234, hlam]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h194, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h199, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h202, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [h203, hlam, p204_0]
                            · have p204_0 := h204c.1
                              have p204_1 := h204c.2.1
                              have p204_2 := h204c.2.2.1
                              have p204_3 := h204c.2.2.2
                              linarith only [hlam, p204_0]
                          · linarith only [h196, h2, h202, h203, hc34, hlam, hphi, u4elo0]
                        · linarith only [h194, h202, hc24, hlam, hphi, u4elo0]
                    · linarith only [h194, h199, h4, hc14, hlam, hphi, u4elo3]
                · linarith only [h196, h3, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h246 | h246
                · linarith only [h1, h195, h246, h4, hc24, hlam, hphi, u4elo3]
                · linarith only [h246, h3, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
              · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                · rcases m.htr 1 3 4 (by decide) (by decide) with h251 | h251
                  · linarith only [h1, h194, h251, h4, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h253 | h253
                    · linarith only [h194, h253, h4, hc03, hlam, hphi, ht34, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h255 | h255
                      · linarith only [h1, h249, h255, h4, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h257 | h257
                        · linarith only [h1, h194, h249, h250, h257, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                          · linarith only [h1, h194, h249, h259, h4, hc23, hlam, hphi, ht34, u4elo3]
                          · linarith only [h1, h249, h259, h4, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h250, h3, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
                · linarith only [h1, h249, h263, h4, hc24, hlam, hphi, u4elo3]
                · linarith only [h263, h3, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h266 | h266
          · rcases m.htr 0 4 5 (by decide) (by decide) with h267 | h267
            · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
              · linarith only [h0, h268, h3, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h270 | h270
                · linarith only [h0, h270, h3, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h273 | h273
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h274 | h274
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h275 | h275
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h276 | h276
                          · rcases h4bigk with h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c | h277c
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [hc14, hlam, hphi, p277_1, u4elo0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h3, hlam, p277_1]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h276, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p277_1, u4elo2]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              rcases p277_3 (m.d 0 4) (by simp) with h282 | h282
                              · rcases p277_3 (m.d 1 4) (by simp) with h283 | h283
                                · linarith only [h2, h283, hlam]
                                · linarith only [h273, h283, hlam]
                              · linarith only [h282, hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h2, hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h270, hlam, p277_1]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h276, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p277_1, u4elo1]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              rcases p277_3 (m.d 0 4) (by simp) with h291 | h291
                              · rcases p277_3 (m.d 1 4) (by simp) with h292 | h292
                                · rcases p277_3 (m.d 2 4) (by simp) with h293 | h293
                                  · rcases p277_3 (m.d 3 4) (by simp) with h294 | h294
                                    · linarith only [h272, h294, hlam]
                                    · linarith only [h276, h294, hlam]
                                  · linarith only [h275, h293, hlam]
                                · linarith only [h292, hlam, p277_0]
                              · linarith only [h267, h291, hlam]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [hc04, hlam, hphi, p277_1, u4elo2]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [hc14, hlam, hphi, p277_1, u4elo2]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h276, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p277_1, u4elo2]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              rcases p277_3 (m.d 0 4) (by simp) with h304 | h304
                              · linarith only [h3, h304, hlam]
                              · linarith only [h267, h304, hlam]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h266, hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h272, hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h274, hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h1, h272, hc01, hc45, hlam, hphi, ht0b, ht5b, p277_1]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h267, hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h273, hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h275, hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [h276, hlam, p277_0]
                            · have p277_0 := h277c.1
                              have p277_1 := h277c.2.1
                              have p277_2 := h277c.2.2.1
                              have p277_3 := h277c.2.2.2
                              linarith only [hlam, p277_0]
                          · linarith only [h267, h276, h3, hc34, hlam, hphi, u4elo2]
                        · linarith only [h2, h273, h275, h3, hlam]
                      · linarith only [h266, h268, h274, h3, hc12, hlam, hphi, ht23, ht34, u4elo2]
                    · linarith only [h267, h273, h3, hc14, hlam, hphi, u4elo2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h322 | h322
                      · linarith only [h268, h272, h322, hc12, hlam, hphi, u2elo2]
                      · linarith only [h268, h322, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h267, h3, h321, hc14, hlam, hphi, u4elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
              · linarith only [h0, h3, h326, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                · linarith only [h0, h267, h3, h328, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h2, h267, h331, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h333 | h333
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h334 | h334
                        · linarith only [h267, h3, h333, h334, hc02, hlam, hphi, u2elo2]
                        · linarith only [h0, h3, h334, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h2, h267, h330, h333, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h266, h267, h330, hc13, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h339 | h339
            · rcases m.htr 1 2 3 (by decide) (by decide) with h340 | h340
              · linarith only [h0, h3, h340, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h342 | h342
                · linarith only [h1, h266, h3, h340, h342, hc02, hlam, hphi, ht23, ht34, u4elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h344 | h344
                  · linarith only [h1, h266, h344, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h346 | h346
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h347 | h347
                      · linarith only [h1, h266, h340, h347, hc12, hlam, hphi, u2elo2]
                      · linarith only [h340, h347, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h3, h339, h346, hc14, hlam, hphi, u4elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h351 | h351
              · linarith only [h0, h3, h351, hc23, hlam, hphi, ht34, u4elo2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h353 | h353
                · linarith only [h0, h3, h339, h353, hc24, hlam, hphi, u4elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                  · linarith only [h1, h266, h339, h355, hc34, hlam, hphi, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h357 | h357
                    · linarith only [h3, h339, h357, hc02, hlam, hphi, ht23, ht34, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h359 | h359
                      · linarith only [h1, h266, h351, h359, hc12, hlam, hphi, u2elo2]
                      · linarith only [h351, h359, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h363 | h363
      · rcases m.htr 0 2 4 (by decide) (by decide) with h364 | h364
        · rcases m.htr 0 3 4 (by decide) (by decide) with h365 | h365
          · rcases m.htr 0 4 5 (by decide) (by decide) with h366 | h366
            · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
              · linarith only [h0, h1, h367, hlam]
              · linarith only [h0, h1, h367, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
              · linarith only [h0, h1, h370, hlam]
              · linarith only [h0, h1, h370, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h365, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h374 | h374
          · rcases m.htr 0 4 5 (by decide) (by decide) with h375 | h375
            · rcases m.htr 1 2 3 (by decide) (by decide) with h376 | h376
              · linarith only [h0, h364, h376, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h1, h376, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h379 | h379
              · linarith only [h0, h364, h375, h379, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h0, h1, h379, hc12, hlam, hphi, u2elo2]
          · linarith only [h0, h1, h374, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · linarith only [h0, h363, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h384 | h384
    · rcases m.htr 0 1 4 (by decide) (by decide) with h385 | h385
      · rcases m.htr 0 2 4 (by decide) (by decide) with h386 | h386
        · rcases m.htr 0 3 4 (by decide) (by decide) with h387 | h387
          · rcases m.htr 0 4 5 (by decide) (by decide) with h388 | h388
            · rcases m.htr 1 2 3 (by decide) (by decide) with h389 | h389
              · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
                · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
                  · linarith only [h0, h384, h391, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h384, h387, h389, h391, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h390, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h389, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
              · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
                · rcases m.htr 1 3 4 (by decide) (by decide) with h398 | h398
                  · linarith only [h0, h384, h398, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h384, h387, h396, h398, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · linarith only [h0, h397, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h384, h387, h396, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h403 | h403
            · rcases m.htr 1 2 3 (by decide) (by decide) with h404 | h404
              · rcases m.htr 1 2 4 (by decide) (by decide) with h405 | h405
                · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                  · linarith only [h0, h384, h406, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h408 | h408
                    · linarith only [h0, h385, h408, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h403, h408, hc14, hlam, hphi, u4elo0]
                · linarith only [h0, h405, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h384, h404, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h413 | h413
              · rcases m.htr 1 2 4 (by decide) (by decide) with h414 | h414
                · rcases m.htr 1 3 4 (by decide) (by decide) with h415 | h415
                  · linarith only [h384, h387, h415, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h417 | h417
                    · linarith only [h0, h385, h403, h417, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                      · linarith only [h384, h387, h413, h419, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
                        · linarith only [h384, h387, h403, h413, h421, hc23, hlam, hphi, ht34, u4elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h423 | h423
                          · linarith only [h384, h387, h403, h413, h423, hc23, hlam, hphi, ht34, u4elo3]
                          · linarith only [h384, h387, h413, h423, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h0, h414, hc01, hlam, hphi, ht12, u2elo3]
              · linarith only [h0, h413, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h0, h384, h386, hc13, hlam, hphi, ht34, u4elo2]
      · linarith only [h384, h385, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h430 | h430
      · rcases m.htr 0 2 4 (by decide) (by decide) with h431 | h431
        · rcases m.htr 0 3 4 (by decide) (by decide) with h432 | h432
          · rcases m.htr 0 4 5 (by decide) (by decide) with h433 | h433
            · rcases m.htr 1 2 3 (by decide) (by decide) with h434 | h434
              · rcases m.htr 1 2 4 (by decide) (by decide) with h435 | h435
                · rcases m.htr 1 3 4 (by decide) (by decide) with h436 | h436
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h437 | h437
                    · linarith only [h384, h430, h434, h437, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · linarith only [h433, h437, hc14, hlam, hphi, u4elo0]
                  · linarith only [h384, h430, h435, h436, hc24, hlam, hphi, u4elo3]
                · linarith only [h384, h430, h434, h435, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
              · linarith only [h0, h434, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
              · rcases m.htr 1 2 4 (by decide) (by decide) with h444 | h444
                · rcases m.htr 1 3 4 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h446 | h446
                    · linarith only [h384, h430, h433, h443, h446, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h448 | h448
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h449 | h449
                        · linarith only [h430, h433, h444, h449, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h451 | h451
                          · linarith only [h430, h433, h444, h448, h451, hlam]
                          · rcases h4bigk with h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h433, hc14, hlam, hphi, p453_1, u4elo4]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h433, h448, hc34, hlam, hphi, p453_1, u4elo4]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h433, hc34, hlam, hphi, p453_1, u4elo4]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h433, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h430, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h384, h430, h443, h448, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p453_1, u2elo1]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h384, h430, h443, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p453_1, u2elo1]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h446, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h431, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h444, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [hc34, hlam, hphi, p453_1, u4elo2]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h449, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h432, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h445, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h448, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h451, hlam, p453_0]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [hc04, hlam, hphi, p453_1, u4elo4]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h444, hc24, hlam, hphi, p453_1, u4elo4]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [h448, hc34, hlam, hphi, p453_1, u4elo4]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [hc34, hlam, hphi, p453_1, u4elo4]
                            · have p453_0 := h453c.1
                              have p453_1 := h453c.2.1
                              have p453_2 := h453c.2.2.1
                              have p453_3 := h453c.2.2.2
                              linarith only [hlam, p453_0]
                      · linarith only [h432, h433, h448, hc23, hlam, hphi, ht34, u4elo4]
                  · linarith only [h384, h432, h433, h445, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                · linarith only [h384, h430, h443, h444, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
              · linarith only [h0, h430, h443, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
          · linarith only [h384, h430, h432, hc14, hlam, hphi, u4elo3]
        · linarith only [h0, h430, h431, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h485 | h485
        · rcases m.htr 0 3 4 (by decide) (by decide) with h486 | h486
          · rcases m.htr 0 4 5 (by decide) (by decide) with h487 | h487
            · rcases m.htr 1 2 3 (by decide) (by decide) with h488 | h488
              · rcases m.htr 1 2 4 (by decide) (by decide) with h489 | h489
                · rcases m.htr 1 3 4 (by decide) (by decide) with h490 | h490
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h491 | h491
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h492 | h492
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h493 | h493
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h494 | h494
                          · linarith only [h488, h492, h494, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h485, h493, h494, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · linarith only [h430, h487, h493, hc24, hlam, hphi, u4elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h498 | h498
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h499 | h499
                          · rcases h4bigk with h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h430, hlam, p500_1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h430, h498, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p500_1, u4elo1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h430, h492, hc23, hlam, hphi, ht34, p500_1, u4elo1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              rcases p500_3 (m.d 0 4) (by simp) with h505 | h505
                              · rcases p500_3 (m.d 1 4) (by simp) with h506 | h506
                                · rcases p500_3 (m.d 2 4) (by simp) with h507 | h507
                                  · linarith only [h485, h507, hlam]
                                  · linarith only [h498, h507, hlam]
                                · linarith only [h491, h506, hlam]
                              · linarith only [h505, hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [hc04, hlam, hphi, p500_1, u4elo1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h384, h486, h488, h492, h498, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht34, ht5b, p500_1, u2elo1, u4elo1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h492, hc23, hlam, hphi, ht34, p500_1, u4elo1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              rcases p500_3 (m.d 0 4) (by simp) with h516 | h516
                              · linarith only [h430, h516, hlam]
                              · linarith only [h487, h516, hlam]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h485, hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h489, hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h492, hlam, p500_1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h0, h485, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p500_1, u2elo1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h486, hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h490, hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h384, h486, h488, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p500_1, u2elo1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h384, h486, h488, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p500_1, u2elo1]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h487, hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h491, hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h498, hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [h499, hlam, p500_0]
                            · have p500_0 := h500c.1
                              have p500_1 := h500c.2.1
                              have p500_2 := h500c.2.2.1
                              have p500_3 := h500c.2.2.2
                              linarith only [hlam, p500_0]
                          · linarith only [h498, h499, hc34, hlam, hphi, u4elo2]
                        · linarith only [h487, h498, hc24, hlam, hphi, u4elo0]
                    · linarith only [h430, h487, h491, hlam]
                  · linarith only [h384, h486, h490, hlam]
                · linarith only [h384, h486, h488, h489, hc34, hlam, hphi, u4elo2]
              · linarith only [h0, h488, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h540 | h540
              · rcases m.htr 1 2 4 (by decide) (by decide) with h541 | h541
                · rcases m.htr 1 3 4 (by decide) (by decide) with h542 | h542
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h543 | h543
                    · linarith only [h487, h543, hc04, hlam, hphi, u4elo1]
                    · linarith only [h430, h543, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h384, h542, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h485, h540, h541, hc23, hlam, hphi, ht34, u4elo0]
              · linarith only [h0, h540, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h549 | h549
            · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
              · rcases m.htr 1 2 4 (by decide) (by decide) with h551 | h551
                · rcases m.htr 1 3 4 (by decide) (by decide) with h552 | h552
                  · linarith only [h384, h486, h550, h552, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h384, h552, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h485, h550, h551, hc23, hlam, hphi, ht34, u4elo0]
              · linarith only [h0, h550, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h557 | h557
              · rcases m.htr 1 2 4 (by decide) (by decide) with h558 | h558
                · rcases m.htr 1 3 4 (by decide) (by decide) with h559 | h559
                  · linarith only [h384, h486, h557, h559, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h384, h559, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                · linarith only [h0, h485, h549, h558, hc02, hlam, hphi, ht23, ht34, u4elo4]
              · linarith only [h0, h557, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h564 | h564
          · rcases m.htr 0 4 5 (by decide) (by decide) with h565 | h565
            · rcases m.htr 1 2 3 (by decide) (by decide) with h566 | h566
              · rcases m.htr 1 2 4 (by decide) (by decide) with h567 | h567
                · linarith only [h485, h567, hc02, hlam, hphi, u2elo1]
                · linarith only [h566, h567, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h566, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h571 | h571
              · rcases m.htr 1 2 4 (by decide) (by decide) with h572 | h572
                · linarith only [h0, h485, h572, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h571, h572, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h571, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h576 | h576
            · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
              · rcases m.htr 1 2 4 (by decide) (by decide) with h578 | h578
                · linarith only [h0, h485, h578, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h577, h578, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h577, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h582 | h582
              · rcases m.htr 1 2 4 (by decide) (by decide) with h583 | h583
                · linarith only [h0, h485, h583, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h582, h583, hc23, hlam, hphi, ht34, u4elo2]
              · linarith only [h0, h582, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
