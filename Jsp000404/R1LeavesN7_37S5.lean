import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7292000 in
set_option maxHeartbeats 7292000 in
theorem r1l7_12_24_L_I_M_LI_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_LI m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
        · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                          · linarith only [h0, h13, h16, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                          · linarith only [h16, h7, hc34, hlam, hphi, u4elo0]
                        · linarith only [h12, h15, h2, hc24, hlam, hphi, u4elo0]
                      · linarith only [h0, h11, h13, h14, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h10, h13, h21, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                          · rcases h2bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h10, h21, h24, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 2) (by simp) with h28 | h28
                              · rcases p25_3 (m.d 1 2) (by simp) with h29 | h29
                                · linarith only [h0, h29, hlam]
                                · linarith only [h29, h8, hlam]
                              · linarith only [h28, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 2) (by simp) with h33 | h33
                              · rcases p25_3 (m.d 1 2) (by simp) with h34 | h34
                                · linarith only [h0, h34, hlam]
                                · linarith only [h34, h9, hlam]
                              · linarith only [h33, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 2) (by simp) with h38 | h38
                              · rcases p25_3 (m.d 1 2) (by simp) with h39 | h39
                                · linarith only [h0, h39, hlam]
                                · linarith only [h10, h21, h23, h24, h39, h8, hc23, hlam, hphi, ht34, u4elo2]
                              · linarith only [h38, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, hlam, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 2) (by simp) with h45 | h45
                              · rcases p25_3 (m.d 1 2) (by simp) with h46 | h46
                                · rcases p25_3 (m.d 2 3) (by simp) with h47 | h47
                                  · linarith only [h47, hlam, p25_0]
                                  · rcases p25_3 (m.d 2 4) (by simp) with h49 | h49
                                    · linarith only [h49, h9, hlam]
                                    · linarith only [h13, h49, hlam]
                                · linarith only [h46, hlam, p25_0]
                              · linarith only [h3, h45, hlam]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h23, hc01, hc45, hlam, hphi, ht0b, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 2) (by simp) with h55 | h55
                              · rcases p25_3 (m.d 1 2) (by simp) with h56 | h56
                                · rcases p25_3 (m.d 2 3) (by simp) with h57 | h57
                                  · linarith only [h57, h8, hlam]
                                  · rcases p25_3 (m.d 2 4) (by simp) with h59 | h59
                                    · linarith only [h59, h9, hlam]
                                    · linarith only [h23, h59, hlam]
                                · linarith only [h56, hlam, p25_0]
                              · linarith only [h5, h55, hlam]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h3, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h8, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h13, hlam, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h21, hlam, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h4, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h9, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, p25_1, u4elo2]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h5, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h10, h13, h5, h8, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h11, h12, h2, h21, hc23, hlam, hphi, ht34, p25_1, u4elo0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h23, hlam, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                          · linarith only [h13, h24, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h12, h2, h23, hc24, hlam, hphi, u4elo0]
                  · linarith only [h12, h7, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h10, h11, h82, hlam]
                  · linarith only [h7, h82, hc14, hlam, hphi, u4elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                · rcases m.htr 1 4 5 (by decide) (by decide) with h86 | h86
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h87 | h87
                    · linarith only [h0, h10, h3, h85, h87, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h89 | h89
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h90 | h90
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h91 | h91
                          · rcases h2bigk with h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c | h92c
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h0, h8, h89, h91, hc01, hc45, hlam, hphi, ht0b, ht5b, p92_1]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              rcases p92_3 (m.d 0 2) (by simp) with h95 | h95
                              · rcases p92_3 (m.d 1 2) (by simp) with h96 | h96
                                · linarith only [h0, h96, hlam]
                                · linarith only [h8, h96, hlam]
                              · linarith only [h95, hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              rcases p92_3 (m.d 0 2) (by simp) with h100 | h100
                              · rcases p92_3 (m.d 1 2) (by simp) with h101 | h101
                                · linarith only [h0, h101, hlam]
                                · linarith only [h101, h9, hlam]
                              · linarith only [h100, hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              rcases p92_3 (m.d 0 2) (by simp) with h105 | h105
                              · rcases p92_3 (m.d 1 2) (by simp) with h106 | h106
                                · linarith only [h0, h106, hlam]
                                · linarith only [h106, h87, h89, h9, hlam]
                              · linarith only [h105, hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h0, hlam, p92_1]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h0, h89, h91, hc01, hc45, hlam, hphi, ht0b, ht5b, p92_1]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h0, h87, h89, h91, hc01, hc45, hlam, hphi, ht0b, ht5b, p92_1]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              rcases p92_3 (m.d 0 2) (by simp) with h114 | h114
                              · rcases p92_3 (m.d 1 2) (by simp) with h115 | h115
                                · rcases p92_3 (m.d 2 3) (by simp) with h116 | h116
                                  · linarith only [h116, h8, hlam]
                                  · linarith only [h116, h89, hlam]
                                · linarith only [h115, hlam, p92_0]
                              · linarith only [h114, h5, hlam]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h3, hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h8, hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h87, hlam, p92_1]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h10, h6, h8, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p92_1, u4elo0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h4, hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h9, hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, p92_1, u4elo2]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h0, h89, h9, h91, hc01, hc45, hlam, hphi, ht0b, ht5b, p92_1]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h5, hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h0, h5, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p92_1]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h89, hlam, p92_0]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [h90, hlam, p92_1]
                            · have p92_0 := h92c.1
                              have p92_1 := h92c.2.1
                              have p92_2 := h92c.2.2.1
                              have p92_3 := h92c.2.2.2
                              linarith only [hlam, p92_0]
                          · linarith only [h10, h91, hc13, hlam, hphi, ht34, u4elo4]
                        · linarith only [h86, h87, h89, h90, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                      · linarith only [h10, h6, h85, h89, hc23, hlam, hphi, ht34, u4elo0]
                  · linarith only [h7, h86, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                    · linarith only [h0, h10, h141, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h143 | h143
                      · linarith only [h143, h8, h85, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h145 | h145
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
                          · rcases h2bigk with h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h0, h145, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p147_1]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              rcases p147_3 (m.d 0 2) (by simp) with h150 | h150
                              · rcases p147_3 (m.d 1 2) (by simp) with h151 | h151
                                · linarith only [h0, h151, hlam]
                                · linarith only [h151, h8, hlam]
                              · linarith only [h150, hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              rcases p147_3 (m.d 0 2) (by simp) with h155 | h155
                              · rcases p147_3 (m.d 1 2) (by simp) with h156 | h156
                                · linarith only [h0, h156, hlam]
                                · linarith only [h156, h9, hlam]
                              · linarith only [h155, hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              rcases p147_3 (m.d 0 2) (by simp) with h160 | h160
                              · rcases p147_3 (m.d 1 2) (by simp) with h161 | h161
                                · linarith only [h0, h161, hlam]
                                · linarith only [h145, h161, h9, hc02, hc45, hlam, hphi, ht0b, ht5b, p147_1]
                              · linarith only [h160, hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h0, hlam, p147_1]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              rcases p147_3 (m.d 0 2) (by simp) with h167 | h167
                              · rcases p147_3 (m.d 1 2) (by simp) with h168 | h168
                                · rcases p147_3 (m.d 2 3) (by simp) with h169 | h169
                                  · linarith only [h169, hlam, p147_0]
                                  · rcases p147_3 (m.d 2 4) (by simp) with h171 | h171
                                    · linarith only [h171, h9, hlam]
                                    · linarith only [h141, h171, hlam]
                                · linarith only [h168, hlam, p147_0]
                              · linarith only [h167, h3, hlam]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h0, h145, hc01, hc45, hlam, hphi, ht0b, ht5b, p147_1]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              rcases p147_3 (m.d 0 2) (by simp) with h177 | h177
                              · rcases p147_3 (m.d 1 2) (by simp) with h178 | h178
                                · rcases p147_3 (m.d 2 3) (by simp) with h179 | h179
                                  · linarith only [h179, h8, hlam]
                                  · rcases p147_3 (m.d 2 4) (by simp) with h181 | h181
                                    · linarith only [h181, h9, hlam]
                                    · linarith only [h145, h181, hlam]
                                · linarith only [h178, hlam, p147_0]
                              · linarith only [h177, h5, hlam]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h3, hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h8, hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h141, hlam, p147_1]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h143, hlam, p147_1]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h4, hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h9, hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h9, hc23, hlam, hphi, ht34, p147_1, u4elo1]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h0, h9, hc01, hc25, hlam, hphi, ht0b, ht5b, p147_1]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h5, hlam, p147_0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h0, h5, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p147_1]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h5, h7, hc23, hlam, hphi, ht34, p147_1, u4elo0]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [h145, hlam, p147_1]
                            · have p147_0 := h147c.1
                              have p147_1 := h147c.2.1
                              have p147_2 := h147c.2.2.1
                              have p147_3 := h147c.2.2.2
                              linarith only [hlam, p147_0]
                          · linarith only [h10, h145, h146, h8, h9, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h10, h140, h145, h6, hc24, hlam, hphi, u4elo0]
                  · linarith only [h140, h7, hc14, hlam, hphi, u4elo0]
            · linarith only [h4, h8, h9, hc23, hlam, hphi, ht34, u4elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
            · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
              · rcases m.htr 1 3 5 (by decide) (by decide) with h207 | h207
                · rcases m.htr 1 4 5 (by decide) (by decide) with h208 | h208
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h209 | h209
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h210 | h210
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h211 | h211
                        · linarith only [h0, h205, h211, h3, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h208, h211, hc24, hlam, hphi, u4elo1]
                      · linarith only [h207, h210, h8, hlam]
                    · linarith only [h209, h8, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h205, h208, h7, hc24, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h217 | h217
                  · linarith only [h205, h207, h217, h8, hlam]
                  · linarith only [h217, h7, hc14, hlam, hphi, u4elo0]
              · linarith only [h205, h206, h8, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
              · rcases m.htr 1 3 5 (by decide) (by decide) with h222 | h222
                · rcases m.htr 1 4 5 (by decide) (by decide) with h223 | h223
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h224 | h224
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h226 | h226
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h227 | h227
                          · rcases h2bigk with h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c | h228c
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              rcases p228_3 (m.d 0 2) (by simp) with h230 | h230
                              · rcases p228_3 (m.d 1 2) (by simp) with h231 | h231
                                · linarith only [h0, h231, hlam]
                                · rcases p228_3 (m.d 2 3) (by simp) with h233 | h233
                                  · linarith only [h233, h3, hlam]
                                  · linarith only [h233, h8, hlam]
                              · linarith only [h0, h230, hlam]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h0, h221, h227, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p228_1]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              rcases p228_3 (m.d 0 2) (by simp) with h238 | h238
                              · rcases p228_3 (m.d 1 2) (by simp) with h239 | h239
                                · linarith only [h0, h239, hlam]
                                · rcases p228_3 (m.d 2 3) (by simp) with h241 | h241
                                  · linarith only [h241, h3, hlam]
                                  · linarith only [h224, h241, hlam]
                              · linarith only [h238, hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              rcases p228_3 (m.d 0 2) (by simp) with h245 | h245
                              · rcases p228_3 (m.d 1 2) (by simp) with h246 | h246
                                · linarith only [h0, h246, hlam]
                                · rcases p228_3 (m.d 2 3) (by simp) with h248 | h248
                                  · linarith only [h248, h3, hlam]
                                  · linarith only [h225, h248, hlam]
                              · linarith only [h245, hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h0, hlam, p228_1]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h8, hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h205, hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h0, h3, h8, hc01, hc25, hlam, hphi, ht0b, ht5b, p228_1]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h3, hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              rcases p228_3 (m.d 0 2) (by simp) with h258 | h258
                              · rcases p228_3 (m.d 1 2) (by simp) with h259 | h259
                                · linarith only [h259, hlam, p228_0]
                                · rcases p228_3 (m.d 2 3) (by simp) with h261 | h261
                                  · rcases p228_3 (m.d 2 4) (by simp) with h262 | h262
                                    · linarith only [h224, h262, hlam]
                                    · linarith only [h205, h262, hlam]
                                  · linarith only [h261, hlam, p228_0]
                              · linarith only [h0, h258, hlam]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h0, h205, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p228_1]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              rcases p228_3 (m.d 0 2) (by simp) with h269 | h269
                              · rcases p228_3 (m.d 1 2) (by simp) with h270 | h270
                                · linarith only [h270, h8, hlam]
                                · rcases p228_3 (m.d 2 3) (by simp) with h272 | h272
                                  · rcases p228_3 (m.d 2 4) (by simp) with h273 | h273
                                    · linarith only [h224, h273, hlam]
                                    · linarith only [h226, h273, hlam]
                                  · linarith only [h225, h272, hlam]
                              · linarith only [h269, h5, hlam]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h4, hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p228_1, u4elo2]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h224, hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              rcases p228_3 (m.d 0 2) (by simp) with h282 | h282
                              · rcases p228_3 (m.d 1 2) (by simp) with h283 | h283
                                · linarith only [h205, h283, hlam]
                                · linarith only [h283, h4, hc12, hlam, hphi, ht23, ht34, p228_1, u4elo0]
                              · linarith only [h282, h5, hlam]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h5, hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h5, h7, hc12, hlam, hphi, ht23, ht34, p228_1, u4elo0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h225, hlam, p228_0]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [h226, hlam, p228_1]
                            · have p228_0 := h228c.1
                              have p228_1 := h228c.2.1
                              have p228_2 := h228c.2.2.1
                              have p228_3 := h228c.2.2.2
                              linarith only [hlam, p228_0]
                          · linarith only [h227, h7, hc34, hlam, hphi, u4elo0]
                        · linarith only [h205, h223, h226, hlam]
                      · linarith only [h222, h225, h8, hlam]
                    · linarith only [h224, h6, h8, hc12, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h223, h7, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h297 | h297
                  · linarith only [h221, h222, h297, hlam]
                  · linarith only [h297, h7, hc14, hlam, hphi, u4elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h300 | h300
                · rcases m.htr 1 4 5 (by decide) (by decide) with h301 | h301
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h302 | h302
                    · linarith only [h0, h221, h3, h300, h302, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h302, h8, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h221, h300, h301, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h306 | h306
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h307 | h307
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h308 | h308
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h309 | h309
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                          · rcases h2bigk with h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h3, h300, h307, h310, h8, hlam, p311_2]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h0, h300, h307, h310, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              rcases p311_3 (m.d 0 2) (by simp) with h315 | h315
                              · rcases p311_3 (m.d 1 2) (by simp) with h316 | h316
                                · linarith only [h0, h316, hlam]
                                · rcases p311_3 (m.d 2 3) (by simp) with h318 | h318
                                  · linarith only [h3, h318, hlam]
                                  · linarith only [h307, h318, hlam]
                              · linarith only [h315, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              rcases p311_3 (m.d 0 2) (by simp) with h322 | h322
                              · rcases p311_3 (m.d 1 2) (by simp) with h323 | h323
                                · linarith only [h0, h323, hlam]
                                · rcases p311_3 (m.d 2 3) (by simp) with h325 | h325
                                  · linarith only [h3, h325, hlam]
                                  · linarith only [h308, h325, hlam]
                              · linarith only [h322, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h0, hlam, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h8, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h205, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h300, h307, h310, h8, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h3, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              rcases p311_3 (m.d 0 2) (by simp) with h335 | h335
                              · rcases p311_3 (m.d 1 2) (by simp) with h336 | h336
                                · linarith only [h336, hlam, p311_0]
                                · rcases p311_3 (m.d 2 3) (by simp) with h338 | h338
                                  · rcases p311_3 (m.d 2 4) (by simp) with h339 | h339
                                    · linarith only [h307, h339, hlam]
                                    · linarith only [h205, h339, hlam]
                                  · linarith only [h338, hlam, p311_0]
                              · linarith only [h0, h335, hlam]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h0, h3, h300, h307, h310, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h0, h3, h300, h308, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h4, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p311_1, u4elo2]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h307, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h300, h308, h4, h8, hc12, hlam, hphi, ht23, ht34, p311_1, u4elo0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h5, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h5, h7, hc12, hlam, hphi, ht23, ht34, p311_1, u4elo0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h308, hlam, p311_0]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [h309, hlam, p311_1]
                            · have p311_0 := h311c.1
                              have p311_1 := h311c.2.1
                              have p311_2 := h311c.2.2.1
                              have p311_3 := h311c.2.2.2
                              linarith only [hlam, p311_0]
                          · linarith only [h306, h310, hc34, hlam, hphi, u4elo1]
                        · linarith only [h0, h221, h3, h306, h307, h309, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h221, h307, h308, h8, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h307, h8, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h306, h7, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h362 | h362
          · rcases m.htr 1 2 4 (by decide) (by decide) with h363 | h363
            · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
              · rcases m.htr 1 3 5 (by decide) (by decide) with h365 | h365
                · rcases m.htr 1 4 5 (by decide) (by decide) with h366 | h366
                  · linarith only [h2, h366, h7, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h368 | h368
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h369 | h369
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h370 | h370
                        · linarith only [h2, h363, h370, h7, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h372 | h372
                          · linarith only [h2, h363, h368, h372, h7, hlam]
                          · rcases h2bigk with h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c | h374c
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h362, h369, h372, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p374_1]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              rcases p374_3 (m.d 0 2) (by simp) with h377 | h377
                              · rcases p374_3 (m.d 1 2) (by simp) with h378 | h378
                                · linarith only [h0, h378, hlam]
                                · linarith only [h362, h378, hlam]
                              · linarith only [h377, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              rcases p374_3 (m.d 0 2) (by simp) with h382 | h382
                              · rcases p374_3 (m.d 1 2) (by simp) with h383 | h383
                                · linarith only [h0, h383, hlam]
                                · linarith only [h363, h383, hlam]
                              · linarith only [h382, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              rcases p374_3 (m.d 0 2) (by simp) with h387 | h387
                              · rcases p374_3 (m.d 1 2) (by simp) with h388 | h388
                                · linarith only [h0, h388, hlam]
                                · linarith only [h362, h369, h372, h388, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p374_1]
                              · linarith only [h387, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h0, hlam, p374_1]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h0, h369, h372, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p374_1]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              rcases p374_3 (m.d 0 2) (by simp) with h395 | h395
                              · rcases p374_3 (m.d 1 2) (by simp) with h396 | h396
                                · rcases p374_3 (m.d 2 3) (by simp) with h397 | h397
                                  · linarith only [h362, h397, hlam]
                                  · linarith only [h368, h397, hlam]
                                · linarith only [h396, hlam, p374_0]
                              · linarith only [h395, h4, hlam]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              rcases p374_3 (m.d 0 2) (by simp) with h402 | h402
                              · rcases p374_3 (m.d 1 2) (by simp) with h403 | h403
                                · rcases p374_3 (m.d 2 3) (by simp) with h404 | h404
                                  · linarith only [h362, h404, hlam]
                                  · linarith only [h369, h404, hlam]
                                · linarith only [h403, hlam, p374_0]
                              · linarith only [h402, h5, hlam]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h3, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h362, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h0, h362, h368, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p374_1]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h0, h362, hc01, hc25, hlam, hphi, ht0b, ht5b, p374_1]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h4, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h363, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h368, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h370, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h5, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h0, h362, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p374_1]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h369, hlam, p374_0]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [h0, h362, h368, h369, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p374_1]
                            · have p374_0 := h374c.1
                              have p374_1 := h374c.2.1
                              have p374_2 := h374c.2.2.1
                              have p374_3 := h374c.2.2.2
                              linarith only [hlam, p374_0]
                      · linarith only [h0, h362, h365, h368, h369, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h368, h6, h7, hc23, hlam, hphi, ht34, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h426 | h426
                  · linarith only [h426, h7, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h428 | h428
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h429 | h429
                      · linarith only [h0, h362, h365, h429, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h431 | h431
                        · linarith only [h2, h363, h431, h7, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h433 | h433
                          · linarith only [h0, h362, h428, h433, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h364, h365, h433, hc34, hlam, hphi, u4elo4]
                    · linarith only [h364, h365, h428, hc23, hc35, hlam, hphi]
              · linarith only [h364, h6, h7, hc13, hlam, hphi, ht34, u4elo4]
            · linarith only [h363, h4, h7, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
            · rcases m.htr 1 3 4 (by decide) (by decide) with h440 | h440
              · rcases m.htr 1 3 5 (by decide) (by decide) with h441 | h441
                · rcases m.htr 1 4 5 (by decide) (by decide) with h442 | h442
                  · linarith only [h2, h442, h7, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h444 | h444
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h445 | h445
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h446 | h446
                        · linarith only [h0, h3, h362, h439, h446, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h448 | h448
                          · linarith only [h2, h439, h444, h448, h7, hlam]
                          · rcases h2bigk with h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c | h450c
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              rcases p450_3 (m.d 0 2) (by simp) with h452 | h452
                              · rcases p450_3 (m.d 1 2) (by simp) with h453 | h453
                                · linarith only [h0, h453, hlam]
                                · rcases p450_3 (m.d 2 3) (by simp) with h455 | h455
                                  · linarith only [h3, h455, hlam]
                                  · linarith only [h362, h455, hlam]
                              · linarith only [h0, h452, hlam]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h0, h362, h439, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h3, h362, h439, hlam, p450_2]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              rcases p450_3 (m.d 0 2) (by simp) with h461 | h461
                              · rcases p450_3 (m.d 1 2) (by simp) with h462 | h462
                                · linarith only [h0, h462, hlam]
                                · rcases p450_3 (m.d 2 3) (by simp) with h464 | h464
                                  · linarith only [h3, h464, hlam]
                                  · linarith only [h445, h464, hlam]
                              · linarith only [h461, hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h0, hlam, p450_1]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h362, hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h0, h3, h362, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h0, h3, h362, hc01, hc25, hlam, hphi, ht0b, ht5b, p450_1]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h3, hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h0, h3, h439, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              rcases p450_3 (m.d 0 2) (by simp) with h476 | h476
                              · rcases p450_3 (m.d 1 2) (by simp) with h477 | h477
                                · linarith only [h362, h477, hlam]
                                · linarith only [h439, h477, hlam]
                              · linarith only [h4, h476, hlam]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              rcases p450_3 (m.d 0 2) (by simp) with h481 | h481
                              · rcases p450_3 (m.d 1 2) (by simp) with h482 | h482
                                · linarith only [h362, h482, hlam]
                                · linarith only [h0, h3, h439, h444, h482, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                              · linarith only [h481, h5, hlam]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h4, hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h439, hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h444, hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h446, hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h5, hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h0, h439, h444, h5, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p450_1]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h445, hlam, p450_0]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [h444, h5, h7, hc34, hlam, hphi, p450_1, u4elo4]
                            · have p450_0 := h450c.1
                              have p450_1 := h450c.2.1
                              have p450_2 := h450c.2.2.1
                              have p450_3 := h450c.2.2.2
                              linarith only [hlam, p450_0]
                      · linarith only [h362, h441, h445, hlam]
                    · linarith only [h362, h441, h444, h6, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h498 | h498
                  · linarith only [h498, h7, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h501 | h501
                      · linarith only [h0, h3, h362, h439, h441, h500, h501, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h362, h439, h5, h500, h501, h7, hc34, hlam, hphi, u4elo4]
                    · linarith only [h362, h500, hc12, hlam, hphi, ht23, ht34, u4elo3]
              · linarith only [h362, h439, h440, h6, hc24, hlam, hphi, u4elo0]
            · linarith only [h4, h439, h7, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h507 | h507
        · rcases m.htr 1 2 3 (by decide) (by decide) with h508 | h508
          · rcases m.htr 1 2 4 (by decide) (by decide) with h509 | h509
            · rcases m.htr 1 3 4 (by decide) (by decide) with h510 | h510
              · linarith only [h1, h510, h6, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h512 | h512
                · rcases m.htr 1 4 5 (by decide) (by decide) with h513 | h513
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h514 | h514
                    · linarith only [h1, h508, h514, h6, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h516 | h516
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h517 | h517
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h518 | h518
                          · rcases h2bigk with h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c | h519c
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h0, h509, h514, h516, h518, hc01, hc45, hlam, hphi, ht0b, ht5b, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              rcases p519_3 (m.d 0 2) (by simp) with h522 | h522
                              · rcases p519_3 (m.d 1 2) (by simp) with h523 | h523
                                · linarith only [h0, h523, hlam]
                                · linarith only [h508, h523, hlam]
                              · linarith only [h522, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              rcases p519_3 (m.d 0 2) (by simp) with h527 | h527
                              · rcases p519_3 (m.d 1 2) (by simp) with h528 | h528
                                · linarith only [h0, h528, hlam]
                                · linarith only [h509, h528, hlam]
                              · linarith only [h527, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              rcases p519_3 (m.d 0 2) (by simp) with h532 | h532
                              · rcases p519_3 (m.d 1 2) (by simp) with h533 | h533
                                · linarith only [h0, h533, hlam]
                                · linarith only [h509, h514, h516, h533, hlam]
                              · linarith only [h532, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h0, hlam, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h0, h516, h518, hc01, hc45, hlam, hphi, ht0b, ht5b, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h0, h514, h516, h518, hc01, hc45, hlam, hphi, ht0b, ht5b, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              rcases p519_3 (m.d 0 2) (by simp) with h541 | h541
                              · rcases p519_3 (m.d 1 2) (by simp) with h542 | h542
                                · rcases p519_3 (m.d 2 3) (by simp) with h543 | h543
                                  · linarith only [h508, h543, hlam]
                                  · linarith only [h516, h543, hlam]
                                · linarith only [h542, hlam, p519_0]
                              · linarith only [h5, h541, hlam]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h3, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h508, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h514, hlam, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h1, h508, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p519_1, u4elo3]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h4, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h509, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, p519_1, u4elo2]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h0, h509, h516, h518, hc01, hc45, hlam, hphi, ht0b, ht5b, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h5, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h0, h5, h509, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h516, hlam, p519_0]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [h517, hlam, p519_1]
                            · have p519_0 := h519c.1
                              have p519_1 := h519c.2.1
                              have p519_2 := h519c.2.2.1
                              have p519_3 := h519c.2.2.2
                              linarith only [hlam, p519_0]
                          · linarith only [h1, h508, h516, h518, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h513, h514, h516, h517, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                      · linarith only [h1, h512, h516, h6, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h507, h513, h6, hc14, hlam, hphi, u4elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                    · linarith only [h0, h508, h568, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h570 | h570
                      · linarith only [h508, h512, h570, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h572 | h572
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h573 | h573
                          · rcases h2bigk with h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c | h574c
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, h509, h572, hc01, hc45, hlam, hphi, ht0b, ht5b, p574_1]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              rcases p574_3 (m.d 0 2) (by simp) with h577 | h577
                              · rcases p574_3 (m.d 1 2) (by simp) with h578 | h578
                                · linarith only [h0, h578, hlam]
                                · linarith only [h508, h578, hlam]
                              · linarith only [h577, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              rcases p574_3 (m.d 0 2) (by simp) with h582 | h582
                              · rcases p574_3 (m.d 1 2) (by simp) with h583 | h583
                                · linarith only [h0, h583, hlam]
                                · linarith only [h509, h583, hlam]
                              · linarith only [h582, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              rcases p574_3 (m.d 0 2) (by simp) with h587 | h587
                              · rcases p574_3 (m.d 1 2) (by simp) with h588 | h588
                                · linarith only [h0, h588, hlam]
                                · linarith only [h509, h572, h588, hc02, hc45, hlam, hphi, ht0b, ht5b, p574_1]
                              · linarith only [h587, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, hlam, p574_1]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              rcases p574_3 (m.d 0 2) (by simp) with h594 | h594
                              · rcases p574_3 (m.d 1 2) (by simp) with h595 | h595
                                · rcases p574_3 (m.d 2 3) (by simp) with h596 | h596
                                  · linarith only [h596, hlam, p574_0]
                                  · rcases p574_3 (m.d 2 4) (by simp) with h598 | h598
                                    · linarith only [h509, h598, hlam]
                                    · linarith only [h568, h598, hlam]
                                · linarith only [h595, hlam, p574_0]
                              · linarith only [h3, h594, hlam]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, h572, hc01, hc45, hlam, hphi, ht0b, ht5b, p574_1]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              rcases p574_3 (m.d 0 2) (by simp) with h604 | h604
                              · rcases p574_3 (m.d 1 2) (by simp) with h605 | h605
                                · rcases p574_3 (m.d 2 3) (by simp) with h606 | h606
                                  · linarith only [h508, h606, hlam]
                                  · rcases p574_3 (m.d 2 4) (by simp) with h608 | h608
                                    · linarith only [h509, h608, hlam]
                                    · linarith only [h572, h608, hlam]
                                · linarith only [h605, hlam, p574_0]
                              · linarith only [h5, h604, hlam]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h3, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h508, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h568, hlam, p574_1]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h570, hlam, p574_1]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h4, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h509, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h2, h509, hc23, hlam, hphi, ht34, p574_1, u4elo0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, h509, hc01, hc25, hlam, hphi, ht0b, ht5b, p574_1]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h5, hlam, p574_0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h0, h5, h509, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p574_1]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h5, h507, hc23, hlam, hphi, ht34, p574_1, u4elo0]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [h572, hlam, p574_1]
                            · have p574_0 := h574c.1
                              have p574_1 := h574c.2.1
                              have p574_2 := h574c.2.2.1
                              have p574_3 := h574c.2.2.2
                              linarith only [hlam, p574_0]
                          · linarith only [h509, h572, h573, h6, hc04, hlam, hphi, u4elo1]
                        · linarith only [h2, h567, h572, hc24, hlam, hphi, u4elo0]
                  · linarith only [h507, h567, h6, hc14, hlam, hphi, u4elo3]
            · linarith only [h4, h508, h509, h6, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h3, h508, h6, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h633 | h633
          · rcases m.htr 1 2 4 (by decide) (by decide) with h634 | h634
            · rcases m.htr 1 3 4 (by decide) (by decide) with h635 | h635
              · linarith only [h1, h507, h6, h635, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h637 | h637
                · rcases m.htr 1 4 5 (by decide) (by decide) with h638 | h638
                  · linarith only [h1, h507, h6, h637, h638, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                  · linarith only [h635, h637, h638, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h641 | h641
                  · linarith only [h507, h6, h641, hc03, hlam, hphi, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h643 | h643
                    · linarith only [h1, h6, h633, h643, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h645 | h645
                      · linarith only [h633, h637, h645, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h647 | h647
                        · linarith only [h1, h507, h6, h633, h647, hc23, hlam, hphi, ht34, u4elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h649 | h649
                          · linarith only [h1, h507, h6, h633, h649, hc23, hlam, hphi, ht34, u4elo3]
                          · linarith only [h1, h6, h633, h649, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h4, h507, h634, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h3, h6, h633, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h654 | h654
      · rcases m.htr 0 4 5 (by decide) (by decide) with h655 | h655
        · linarith only [h4, h5, h655, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h657 | h657
          · rcases m.htr 1 2 4 (by decide) (by decide) with h658 | h658
            · rcases m.htr 1 3 4 (by decide) (by decide) with h659 | h659
              · rcases m.htr 1 3 5 (by decide) (by decide) with h660 | h660
                · rcases m.htr 1 4 5 (by decide) (by decide) with h661 | h661
                  · linarith only [h2, h655, h661, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h663 | h663
                    · linarith only [h0, h5, h655, h657, h663, hc34, hlam, hphi, u4elo4]
                    · linarith only [h1, h3, h5, h655, h659, h663, hc23, hlam, hphi, ht34, u4elo4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h666 | h666
                  · linarith only [h2, h655, h666, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h668 | h668
                    · linarith only [h3, h5, h655, h668, hc34, hlam, hphi, u4elo4]
                    · linarith only [h3, h5, h654, h655, h668, hc23, hlam, hphi, ht34, u4elo4]
              · linarith only [h3, h5, h654, h655, h659, hc13, hlam, hphi, ht34, u4elo4]
            · linarith only [h4, h5, h655, h658, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h3, h5, h655, h657, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h674 | h674
        · linarith only [h4, h5, h674, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h676 | h676
          · rcases m.htr 1 2 4 (by decide) (by decide) with h677 | h677
            · rcases m.htr 1 3 4 (by decide) (by decide) with h678 | h678
              · linarith only [h1, h654, h674, h678, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h680 | h680
                · rcases m.htr 1 4 5 (by decide) (by decide) with h681 | h681
                  · linarith only [h2, h674, h681, hlam]
                  · linarith only [h678, h680, h681, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h684 | h684
                  · linarith only [h654, h674, h684, hc03, hlam, hphi, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h686 | h686
                    · linarith only [h1, h654, h676, h686, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h688 | h688
                      · linarith only [h676, h680, h688, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h690 | h690
                        · linarith only [h3, h5, h674, h690, hc23, hlam, hphi, ht34, u4elo2]
                        · linarith only [h0, h5, h677, h686, h690, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h4, h5, h677, hc12, hc25, hlam, hphi]
          · linarith only [h3, h5, h676, hc12, hc25, hlam, hphi]
  · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]

end R2N4
