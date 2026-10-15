import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7592000 in
set_option maxHeartbeats 7592000 in
theorem r1l7_13_24_L_I_M_LI_x0_x0_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3bigk := hb3.1
  have h3emin := hb3.2.1
  have h4elo := hb4.1
  have h4bigk := hb4.2.2.2
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
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
                      · linarith only [h1, h10, h13, h21, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h23 | h23
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                          · rcases h3bigk with h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c | h25c
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h10, h21, h24, h3, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 3) (by simp) with h28 | h28
                              · rcases p25_3 (m.d 1 3) (by simp) with h29 | h29
                                · linarith only [h1, h29, hlam]
                                · linarith only [h29, h8, hlam]
                              · linarith only [h28, h3, hlam]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 3) (by simp) with h33 | h33
                              · rcases p25_3 (m.d 1 3) (by simp) with h34 | h34
                                · linarith only [h1, h34, hlam]
                                · linarith only [h10, h34, hlam]
                              · linarith only [h33, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 3) (by simp) with h38 | h38
                              · rcases p25_3 (m.d 1 3) (by simp) with h39 | h39
                                · linarith only [h1, h39, hlam]
                                · linarith only [h11, h39, hlam]
                              · linarith only [h38, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h1, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              rcases p25_3 (m.d 0 3) (by simp) with h45 | h45
                              · rcases p25_3 (m.d 1 3) (by simp) with h46 | h46
                                · rcases p25_3 (m.d 2 3) (by simp) with h47 | h47
                                  · linarith only [h47, h8, hlam]
                                  · rcases p25_3 (m.d 3 4) (by simp) with h49 | h49
                                    · linarith only [h10, h49, hlam]
                                    · linarith only [h13, h49, hlam]
                                · linarith only [h46, h8, hlam]
                              · linarith only [h3, h45, hlam]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h21, h24, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h0, h21, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p25_1]
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
                              linarith only [h13, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h21, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h5, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h10, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, p25_1, u4elo3]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h21, hc23, hc34, hlam, hphi, p25_1]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h6, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h11, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h6, h7, hc23, hlam, hphi, ht34, p25_1, u4elo0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [h24, hlam, p25_0]
                            · have p25_0 := h25c.1
                              have p25_1 := h25c.2.1
                              have p25_2 := h25c.2.2.1
                              have p25_3 := h25c.2.2.2
                              linarith only [hlam, p25_0]
                          · linarith only [h23, h24, hc34, hlam, hphi, u4elo2]
                        · linarith only [h12, h2, h23, hc24, hlam, hphi, u4elo0]
                  · linarith only [h12, h7, hc14, hlam, hphi, u4elo0]
                · linarith only [h10, h11, h6, h7, hc34, hlam, hphi, u4elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h75 | h75
                · rcases m.htr 1 4 5 (by decide) (by decide) with h76 | h76
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h77 | h77
                    · linarith only [h10, h75, h77, h8, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h79 | h79
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h80 | h80
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                          · rcases h3bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              rcases p82_3 (m.d 0 3) (by simp) with h84 | h84
                              · rcases p82_3 (m.d 1 3) (by simp) with h85 | h85
                                · linarith only [h1, h85, hlam]
                                · rcases p82_3 (m.d 2 3) (by simp) with h87 | h87
                                  · linarith only [h3, h87, hlam]
                                  · rcases p82_3 (m.d 3 4) (by simp) with h89 | h89
                                    · linarith only [h5, h89, hlam]
                                    · linarith only [h10, h89, hlam]
                              · linarith only [h1, h84, hlam]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              rcases p82_3 (m.d 0 3) (by simp) with h93 | h93
                              · rcases p82_3 (m.d 1 3) (by simp) with h94 | h94
                                · linarith only [h1, h94, hlam]
                                · linarith only [h8, h94, hlam]
                              · linarith only [h3, h93, hlam]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h0, h10, h3, h79, h8, h81, hc01, hc45, hlam, hphi, ht0b, ht5b, p82_1]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h10, h5, h79, h8, hlam, p82_2]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h1, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h10, h5, h79, h81, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p82_1, u4elo0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h10, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h10, h5, h81, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p82_1, u4elo0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h3, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h8, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h77, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h0, h8, h81, hc01, hc45, hlam, hphi, ht0b, ht5b, p82_1]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h5, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h5, hc13, hlam, hphi, ht34, p82_1, u4elo0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h5, hc23, hlam, hphi, ht34, p82_1, u4elo0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              rcases p82_3 (m.d 0 3) (by simp) with h114 | h114
                              · rcases p82_3 (m.d 1 3) (by simp) with h115 | h115
                                · linarith only [h10, h115, hlam]
                                · linarith only [h115, h75, hlam]
                              · linarith only [h114, h6, hlam]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h6, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h75, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h79, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [h81, hlam, p82_0]
                            · have p82_0 := h82c.1
                              have p82_1 := h82c.2.1
                              have p82_2 := h82c.2.2.1
                              have p82_3 := h82c.2.2.2
                              linarith only [hlam, p82_0]
                          · linarith only [h10, h81, hc13, hlam, hphi, ht34, u4elo4]
                        · linarith only [h76, h80, hc24, hlam, hphi, u4elo1]
                      · linarith only [h10, h5, h75, h79, hc23, hlam, hphi, ht34, u4elo0]
                  · linarith only [h7, h76, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h128 | h128
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h129 | h129
                    · linarith only [h129, h6, h7, h75, h8, hc34, hlam, hphi, u4elo0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h131 | h131
                      · linarith only [h129, h131, h75, hc13, hlam, hphi, ht34, u4elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                          · rcases h3bigk with h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              rcases p135_3 (m.d 0 3) (by simp) with h137 | h137
                              · rcases p135_3 (m.d 1 3) (by simp) with h138 | h138
                                · linarith only [h1, h138, hlam]
                                · rcases p135_3 (m.d 2 3) (by simp) with h140 | h140
                                  · linarith only [h140, h3, hlam]
                                  · rcases p135_3 (m.d 3 4) (by simp) with h142 | h142
                                    · linarith only [h142, h5, hlam]
                                    · linarith only [h10, h142, hlam]
                              · linarith only [h1, h137, hlam]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              rcases p135_3 (m.d 0 3) (by simp) with h146 | h146
                              · rcases p135_3 (m.d 1 3) (by simp) with h147 | h147
                                · linarith only [h1, h147, hlam]
                                · linarith only [h147, h8, hlam]
                              · linarith only [h146, h3, hlam]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              rcases p135_3 (m.d 0 3) (by simp) with h151 | h151
                              · rcases p135_3 (m.d 1 3) (by simp) with h152 | h152
                                · linarith only [h1, h152, hlam]
                                · rcases p135_3 (m.d 2 3) (by simp) with h154 | h154
                                  · linarith only [h154, h3, hlam]
                                  · rcases p135_3 (m.d 3 4) (by simp) with h156 | h156
                                    · linarith only [h156, hlam, p135_0]
                                    · rcases p135_3 (m.d 3 5) (by simp) with h158 | h158
                                      · linarith only [h158, h6, hlam]
                                      · rcases h3emin with h160 | h160 | h160 | h160 | h160
                                        · rcases h4bigk with h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [hlam, p161_0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h0, h133, h134, h3, h75, h8, h9, hc01, hc23, hc45, hlam, hphi, ht0b, ht34, ht5b, p135_1, p161_1, u4elo0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h0, h133, h134, h3, h75, h8, hc01, hc23, hc45, hlam, hphi, ht0b, ht34, ht5b, p135_1, p161_1, u4elo0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h134, h75, h8, hc23, hlam, hphi, ht34, p161_1, u4elo0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            rcases p161_3 (m.d 0 4) (by simp) with h166 | h166
                                            · rcases p161_3 (m.d 1 4) (by simp) with h167 | h167
                                              · linarith only [h167, h2, hlam]
                                              · linarith only [h128, h167, hlam]
                                            · linarith only [h166, hlam, p161_0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h2, hlam, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [hlam, p161_0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h0, h133, h134, h3, h75, h8, hc01, hc23, hc45, hlam, hphi, ht0b, ht34, ht5b, p135_1, p161_1, u4elo1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h10, hlam, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h0, h10, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p135_1, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h4, hlam, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h9, hlam, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [hlam, p161_0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h129, hlam, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h0, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h5, hlam, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h0, h3, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p135_1, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h0, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p135_1, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [hlam, p161_0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h0, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p135_1, p161_1]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h7, hlam, p161_0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h128, hlam, p161_0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h133, hlam, p161_0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [h134, hlam, p161_0]
                                          · have p161_0 := h161c.1
                                            have p161_1 := h161c.2.1
                                            have p161_2 := h161c.2.2.1
                                            have p161_3 := h161c.2.2.2
                                            linarith only [hlam, p161_0]
                                        · linarith only [h0, h134, h160, h3, h75, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p135_1]
                                        · linarith only [h0, h134, h160, h3, h75, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p135_1]
                                        · linarith only [h0, h160, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p135_1]
                                        · linarith only [h0, h134, h160, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p135_1]
                              · linarith only [h151, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              rcases p135_3 (m.d 0 3) (by simp) with h196 | h196
                              · rcases p135_3 (m.d 1 3) (by simp) with h197 | h197
                                · linarith only [h1, h197, hlam]
                                · rcases p135_3 (m.d 2 3) (by simp) with h199 | h199
                                  · linarith only [h199, h3, hlam]
                                  · rcases p135_3 (m.d 3 4) (by simp) with h201 | h201
                                    · linarith only [h201, h5, hlam]
                                    · linarith only [h134, h201, hlam]
                              · linarith only [h196, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h1, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h134, h75, hc23, hc34, hlam, hphi, p135_1]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h10, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h75, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h3, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h8, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h129, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h131, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h5, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h5, hc13, hlam, hphi, ht34, p135_1, u4elo0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h5, hc23, hlam, hphi, ht34, p135_1, u4elo0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h5, h75, h8, hc23, hlam, hphi, ht34, p135_1, u4elo0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h6, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h6, h7, h8, hc23, hlam, hphi, ht34, p135_1, u4elo0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h6, h7, hc23, hlam, hphi, ht34, p135_1, u4elo0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h134, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [hlam, p135_0]
                          · linarith only [h133, h134, h9, hc34, hlam, hphi, u4elo1]
                        · linarith only [h133, h7, hc24, hlam, hphi, u4elo0]
                  · linarith only [h128, h7, hc14, hlam, hphi, u4elo0]
            · linarith only [h4, h8, h9, hc23, hlam, hphi, ht34, u4elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h229 | h229
            · rcases m.htr 1 3 4 (by decide) (by decide) with h230 | h230
              · rcases m.htr 1 3 5 (by decide) (by decide) with h231 | h231
                · rcases m.htr 1 4 5 (by decide) (by decide) with h232 | h232
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h234 | h234
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h235 | h235
                        · linarith only [h0, h229, h235, h3, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · linarith only [h232, h235, hc24, hlam, hphi, u4elo1]
                      · linarith only [h229, h231, h232, h234, h8, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h233, h5, h8, hc12, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h232, h7, hc14, hlam, hphi, u4elo0]
                · linarith only [h229, h231, h6, h7, h8, hc24, hlam, hphi, u4elo0]
              · linarith only [h229, h230, h8, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
              · rcases m.htr 1 3 5 (by decide) (by decide) with h244 | h244
                · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h247 | h247
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h249 | h249
                          · rcases h3bigk with h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c | h250c
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h0, h243, h249, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p250_1]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h0, h243, h249, h3, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p250_1]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              rcases p250_3 (m.d 0 3) (by simp) with h254 | h254
                              · rcases p250_3 (m.d 1 3) (by simp) with h255 | h255
                                · linarith only [h1, h255, hlam]
                                · linarith only [h243, h255, hlam]
                              · linarith only [h254, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              rcases p250_3 (m.d 0 3) (by simp) with h259 | h259
                              · rcases p250_3 (m.d 1 3) (by simp) with h260 | h260
                                · linarith only [h1, h260, hlam]
                                · linarith only [h244, h260, hlam]
                              · linarith only [h259, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h1, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h8, hlam, p250_1]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h1, h249, hc01, hc45, hlam, hphi, ht0b, ht5b, p250_1]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              rcases p250_3 (m.d 0 3) (by simp) with h268 | h268
                              · rcases p250_3 (m.d 1 3) (by simp) with h269 | h269
                                · rcases p250_3 (m.d 2 3) (by simp) with h270 | h270
                                  · rcases p250_3 (m.d 3 4) (by simp) with h271 | h271
                                    · linarith only [h243, h271, hlam]
                                    · linarith only [h249, h271, hlam]
                                  · linarith only [h247, h270, hlam]
                                · linarith only [h269, hlam, p250_0]
                              · linarith only [h268, h6, hlam]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h3, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h0, h243, h249, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p250_1]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h0, h249, h3, hc01, hc45, hlam, hphi, ht0b, ht5b, p250_1]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              rcases p250_3 (m.d 0 3) (by simp) with h281 | h281
                              · rcases p250_3 (m.d 1 3) (by simp) with h282 | h282
                                · linarith only [h282, h8, hlam]
                                · linarith only [h244, h282, hlam]
                              · linarith only [h281, h6, hlam]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h5, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h243, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h246, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h1, h243, h249, hc01, hc45, hlam, hphi, ht0b, ht5b, p250_1]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h6, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h244, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h247, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [h249, hlam, p250_0]
                            · have p250_0 := h250c.1
                              have p250_1 := h250c.2.1
                              have p250_2 := h250c.2.2.1
                              have p250_3 := h250c.2.2.2
                              linarith only [hlam, p250_0]
                          · linarith only [h249, h7, hc34, hlam, hphi, u4elo0]
                        · linarith only [h229, h245, h248, hlam]
                      · linarith only [h247, h6, h7, h8, hc12, hlam, hphi, ht23, ht34, u4elo0]
                    · linarith only [h246, h5, h8, hc12, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h245, h7, hc14, hlam, hphi, u4elo0]
                · linarith only [h243, h244, h6, h7, hc34, hlam, hphi, u4elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h302 | h302
                · rcases m.htr 1 4 5 (by decide) (by decide) with h303 | h303
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h304 | h304
                    · linarith only [h0, h243, h3, h302, h304, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h304, h5, h8, hc12, hlam, hphi, ht23, ht34, u4elo0]
                  · linarith only [h243, h302, h303, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h311 | h311
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h312 | h312
                          · rcases h3bigk with h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c | h313c
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              rcases p313_3 (m.d 0 3) (by simp) with h315 | h315
                              · rcases p313_3 (m.d 1 3) (by simp) with h316 | h316
                                · linarith only [h1, h316, hlam]
                                · rcases p313_3 (m.d 2 3) (by simp) with h318 | h318
                                  · linarith only [h3, h318, hlam]
                                  · linarith only [h318, h8, hlam]
                              · linarith only [h1, h315, hlam]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h302, h309, h312, h8, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p313_1]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              rcases p313_3 (m.d 0 3) (by simp) with h323 | h323
                              · rcases p313_3 (m.d 1 3) (by simp) with h324 | h324
                                · linarith only [h1, h324, hlam]
                                · rcases p313_3 (m.d 2 3) (by simp) with h326 | h326
                                  · linarith only [h3, h326, hlam]
                                  · linarith only [h309, h326, hlam]
                              · linarith only [h323, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              rcases p313_3 (m.d 0 3) (by simp) with h330 | h330
                              · rcases p313_3 (m.d 1 3) (by simp) with h331 | h331
                                · linarith only [h1, h331, hlam]
                                · rcases p313_3 (m.d 2 3) (by simp) with h333 | h333
                                  · linarith only [h3, h333, hlam]
                                  · linarith only [h310, h333, hlam]
                              · linarith only [h330, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h1, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h8, hlam, p313_1]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h243, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h302, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h3, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              rcases p313_3 (m.d 0 3) (by simp) with h343 | h343
                              · rcases p313_3 (m.d 1 3) (by simp) with h344 | h344
                                · linarith only [h344, h8, hlam]
                                · rcases p313_3 (m.d 2 3) (by simp) with h346 | h346
                                  · rcases p313_3 (m.d 3 4) (by simp) with h347 | h347
                                    · linarith only [h309, h347, hlam]
                                    · linarith only [h243, h347, hlam]
                                  · linarith only [h346, h8, hlam]
                              · linarith only [h1, h343, hlam]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h302, h312, h8, hc12, hc23, hlam, hphi, p313_1]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h0, h3, h302, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p313_1]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h5, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h8, hc12, hlam, hphi, ht23, ht34, p313_1, u4elo3]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h309, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h0, h3, h302, h309, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p313_1]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h6, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h6, h7, h8, hc12, hlam, hphi, ht23, ht34, p313_1, u4elo0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h310, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [h312, hlam, p313_0]
                            · have p313_0 := h313c.1
                              have p313_1 := h313c.2.1
                              have p313_2 := h313c.2.2.1
                              have p313_3 := h313c.2.2.2
                              linarith only [hlam, p313_0]
                          · linarith only [h308, h312, hc34, hlam, hphi, u4elo1]
                        · linarith only [h0, h243, h3, h308, h309, h311, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h243, h3, h308, h309, h310, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · linarith only [h309, h8, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h308, h7, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
          · rcases m.htr 1 2 4 (by decide) (by decide) with h371 | h371
            · rcases m.htr 1 3 4 (by decide) (by decide) with h372 | h372
              · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
                · rcases m.htr 1 4 5 (by decide) (by decide) with h374 | h374
                  · linarith only [h374, h7, hc04, hlam, hphi, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h376 | h376
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h377 | h377
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                        · linarith only [h2, h371, h378, h7, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h380 | h380
                          · linarith only [h0, h370, h376, h380, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h3bigk with h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              rcases p382_3 (m.d 0 3) (by simp) with h384 | h384
                              · rcases p382_3 (m.d 1 3) (by simp) with h385 | h385
                                · linarith only [h1, h385, hlam]
                                · rcases p382_3 (m.d 2 3) (by simp) with h387 | h387
                                  · linarith only [h3, h387, hlam]
                                  · rcases p382_3 (m.d 3 4) (by simp) with h389 | h389
                                    · linarith only [h389, h5, hlam]
                                    · rcases p382_3 (m.d 3 5) (by simp) with h391 | h391
                                      · linarith only [h391, h6, hlam]
                                      · rcases h3emin with h393 | h393 | h393 | h393 | h393
                                        · rcases h4bigk with h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c | h394c
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h371, h376, h7, hc34, hlam, hphi, p394_1, u4elo4]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h376, h7, hc34, hlam, hphi, p394_1, u4elo4]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h7, hc34, hlam, hphi, p394_1, u4elo4]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h7, hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h2, hlam, p394_1]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h376, hc34, hlam, hphi, p394_1, u4elo1]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h2, h7, hc34, hlam, hphi, p394_1, u4elo4]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h374, hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h4, hlam, p394_1]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h371, hlam, p394_1]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [hc34, hlam, hphi, p394_1, u4elo2]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h378, hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h5, hlam, p394_1]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h372, hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h376, hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h380, hlam, p394_0]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [hc04, hlam, hphi, p394_1, u4elo4]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h371, hc24, hlam, hphi, p394_1, u4elo4]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [h376, hc34, hlam, hphi, p394_1, u4elo4]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [hc34, hlam, hphi, p394_1, u4elo4]
                                          · have p394_0 := h394c.1
                                            have p394_1 := h394c.2.1
                                            have p394_2 := h394c.2.2.1
                                            have p394_3 := h394c.2.2.2
                                            linarith only [hlam, p394_0]
                                        · linarith only [h0, h3, h393, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p382_1]
                                        · linarith only [h0, h3, h370, h393, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p382_1]
                                        · linarith only [h2, h371, h376, h393, hlam, ht34, u4elo0]
                                        · linarith only [h393, h6, h7, hlam, ht34, u4elo4]
                              · linarith only [h1, h384, hlam]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              rcases p382_3 (m.d 0 3) (by simp) with h425 | h425
                              · rcases p382_3 (m.d 1 3) (by simp) with h426 | h426
                                · linarith only [h1, h426, hlam]
                                · linarith only [h370, h426, hlam]
                              · linarith only [h3, h425, hlam]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              rcases p382_3 (m.d 0 3) (by simp) with h430 | h430
                              · rcases p382_3 (m.d 1 3) (by simp) with h431 | h431
                                · linarith only [h1, h431, hlam]
                                · linarith only [h372, h431, hlam]
                              · linarith only [h430, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              rcases p382_3 (m.d 0 3) (by simp) with h435 | h435
                              · rcases p382_3 (m.d 1 3) (by simp) with h436 | h436
                                · linarith only [h1, h436, hlam]
                                · linarith only [h373, h436, hlam]
                              · linarith only [h435, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h1, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h1, h377, h380, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p382_1]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              rcases p382_3 (m.d 0 3) (by simp) with h443 | h443
                              · rcases p382_3 (m.d 1 3) (by simp) with h444 | h444
                                · rcases p382_3 (m.d 2 3) (by simp) with h445 | h445
                                  · linarith only [h370, h445, hlam]
                                  · linarith only [h376, h445, hlam]
                                · linarith only [h444, hlam, p382_0]
                              · linarith only [h443, h5, hlam]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              rcases p382_3 (m.d 0 3) (by simp) with h450 | h450
                              · rcases p382_3 (m.d 1 3) (by simp) with h451 | h451
                                · rcases p382_3 (m.d 2 3) (by simp) with h452 | h452
                                  · linarith only [h370, h452, hlam]
                                  · linarith only [h377, h452, hlam]
                                · linarith only [h451, hlam, p382_0]
                              · linarith only [h450, h6, hlam]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h3, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h370, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h0, h370, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p382_1]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h0, h370, h380, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p382_1]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h5, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h372, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h376, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h380, hlam, p382_1]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h6, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h373, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h377, hlam, p382_0]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [h6, h7, hc34, hlam, hphi, p382_1, u4elo4]
                            · have p382_0 := h382c.1
                              have p382_1 := h382c.2.1
                              have p382_2 := h382c.2.2.1
                              have p382_3 := h382c.2.2.2
                              linarith only [hlam, p382_0]
                      · linarith only [h0, h370, h373, h376, h377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h376, h5, h7, hc23, hlam, hphi, ht34, u4elo4]
                · linarith only [h372, h373, h6, h7, hc34, hlam, hphi, u4elo4]
              · linarith only [h372, h5, h7, hc13, hlam, hphi, ht34, u4elo4]
            · linarith only [h371, h4, h7, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h477 | h477
            · rcases m.htr 1 3 4 (by decide) (by decide) with h478 | h478
              · rcases m.htr 1 3 5 (by decide) (by decide) with h479 | h479
                · rcases m.htr 1 4 5 (by decide) (by decide) with h480 | h480
                  · linarith only [h2, h480, h7, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h482 | h482
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h483 | h483
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h484 | h484
                        · linarith only [h2, h370, h477, h484, h7, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h486 | h486
                          · linarith only [h2, h477, h482, h486, h7, hlam]
                          · rcases h3bigk with h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c | h488c
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              rcases p488_3 (m.d 0 3) (by simp) with h490 | h490
                              · rcases p488_3 (m.d 1 3) (by simp) with h491 | h491
                                · linarith only [h1, h491, hlam]
                                · rcases p488_3 (m.d 2 3) (by simp) with h493 | h493
                                  · linarith only [h3, h493, hlam]
                                  · linarith only [h370, h493, hlam]
                              · linarith only [h1, h490, hlam]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h0, h3, h370, h477, h482, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p488_1]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              rcases p488_3 (m.d 0 3) (by simp) with h498 | h498
                              · rcases p488_3 (m.d 1 3) (by simp) with h499 | h499
                                · linarith only [h1, h499, hlam]
                                · linarith only [h478, h499, hlam]
                              · linarith only [h498, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              rcases p488_3 (m.d 0 3) (by simp) with h503 | h503
                              · rcases p488_3 (m.d 1 3) (by simp) with h504 | h504
                                · linarith only [h1, h504, hlam]
                                · linarith only [h479, h504, hlam]
                              · linarith only [h503, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h1, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h370, hlam, p488_1]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              rcases p488_3 (m.d 0 3) (by simp) with h511 | h511
                              · rcases p488_3 (m.d 1 3) (by simp) with h512 | h512
                                · rcases p488_3 (m.d 2 3) (by simp) with h513 | h513
                                  · rcases p488_3 (m.d 3 4) (by simp) with h514 | h514
                                    · linarith only [h514, hlam, p488_0]
                                    · rcases p488_3 (m.d 3 5) (by simp) with h516 | h516
                                      · linarith only [h479, h516, hlam]
                                      · linarith only [h486, h516, hlam]
                                  · linarith only [h482, h513, hlam]
                                · linarith only [h512, hlam, p488_0]
                              · linarith only [h5, h511, hlam]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              rcases p488_3 (m.d 0 3) (by simp) with h522 | h522
                              · rcases p488_3 (m.d 1 3) (by simp) with h523 | h523
                                · rcases p488_3 (m.d 2 3) (by simp) with h524 | h524
                                  · rcases p488_3 (m.d 3 4) (by simp) with h525 | h525
                                    · linarith only [h478, h525, hlam]
                                    · rcases p488_3 (m.d 3 5) (by simp) with h527 | h527
                                      · linarith only [h527, hlam, p488_0]
                                      · rcases h3emin with h529 | h529 | h529 | h529 | h529
                                        · rcases h4bigk with h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h477, h482, h7, hc34, hlam, hphi, p530_1, u4elo4]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h482, h7, hc34, hlam, hphi, p530_1, u4elo4]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h7, hc34, hlam, hphi, p530_1, u4elo4]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h7, hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h2, hlam, p530_1]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h482, hc34, hlam, hphi, p530_1, u4elo1]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h2, h7, hc34, hlam, hphi, p530_1, u4elo4]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h480, hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h4, hlam, p530_1]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h477, hlam, p530_1]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [hc34, hlam, hphi, p530_1, u4elo2]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h484, hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h5, hlam, p530_1]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h478, hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h482, hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h486, hlam, p530_0]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [hc04, hlam, hphi, p530_1, u4elo4]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h477, hc24, hlam, hphi, p530_1, u4elo4]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [h482, hc34, hlam, hphi, p530_1, u4elo4]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [hc34, hlam, hphi, p530_1, u4elo4]
                                          · have p530_0 := h530c.1
                                            have p530_1 := h530c.2.1
                                            have p530_2 := h530c.2.2.1
                                            have p530_3 := h530c.2.2.2
                                            linarith only [hlam, p530_0]
                                        · rcases h4bigk with h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h477, h482, hc34, hlam, hphi, p556_1, u4elo0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h482, hc34, hlam, hphi, p556_1, u4elo0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [hc34, hlam, hphi, p556_1, u4elo0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h7, hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h2, hlam, p556_1]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h482, hc34, hlam, hphi, p556_1, u4elo1]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h2, h7, hc34, hlam, hphi, p556_1, u4elo4]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h480, hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h4, hlam, p556_1]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h477, hlam, p556_1]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [hc34, hlam, hphi, p556_1, u4elo2]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h484, hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h5, hlam, p556_1]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h478, hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h482, hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h486, hlam, p556_0]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [hc04, hlam, hphi, p556_1, u4elo4]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h477, hc24, hlam, hphi, p556_1, u4elo4]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [h482, hc34, hlam, hphi, p556_1, u4elo4]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [hc34, hlam, hphi, p556_1, u4elo4]
                                          · have p556_0 := h556c.1
                                            have p556_1 := h556c.2.1
                                            have p556_2 := h556c.2.2.1
                                            have p556_3 := h556c.2.2.2
                                            linarith only [hlam, p556_0]
                                        · rcases h4bigk with h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c | h582c
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h477, h482, h7, hc34, hlam, hphi, p582_1, u4elo4]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h482, h7, hc34, hlam, hphi, p582_1, u4elo4]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h7, hc34, hlam, hphi, p582_1, u4elo4]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h7, hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h2, hlam, p582_1]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h482, hc34, hlam, hphi, p582_1, u4elo1]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h2, h7, hc34, hlam, hphi, p582_1, u4elo4]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h480, hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h4, hlam, p582_1]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h477, hlam, p582_1]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [hc34, hlam, hphi, p582_1, u4elo2]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h484, hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h5, hlam, p582_1]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h478, hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h482, hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h486, hlam, p582_0]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [hc04, hlam, hphi, p582_1, u4elo4]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [hc14, hlam, hphi, p582_1, u4elo4]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [h482, hc34, hlam, hphi, p582_1, u4elo4]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [hc34, hlam, hphi, p582_1, u4elo4]
                                          · have p582_0 := h582c.1
                                            have p582_1 := h582c.2.1
                                            have p582_2 := h582c.2.2.1
                                            have p582_3 := h582c.2.2.2
                                            linarith only [hlam, p582_0]
                                        · linarith only [h3, h370, h486, h529, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p488_1]
                                        · linarith only [h370, h529, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p488_1]
                                  · linarith only [h483, h524, hlam]
                                · linarith only [h523, hlam, p488_0]
                              · linarith only [h522, h6, hlam]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h3, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h0, h3, h370, h477, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p488_1]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              rcases p488_3 (m.d 0 3) (by simp) with h616 | h616
                              · rcases p488_3 (m.d 1 3) (by simp) with h617 | h617
                                · linarith only [h370, h617, hlam]
                                · linarith only [h478, h617, hlam]
                              · linarith only [h5, h616, hlam]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              rcases p488_3 (m.d 0 3) (by simp) with h621 | h621
                              · rcases p488_3 (m.d 1 3) (by simp) with h622 | h622
                                · linarith only [h370, h622, hlam]
                                · linarith only [h479, h622, hlam]
                              · linarith only [h6, h621, hlam]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h5, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h478, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h482, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h486, hlam, p488_1]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h6, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h479, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h483, hlam, p488_0]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [h6, h7, hc34, hlam, hphi, p488_1, u4elo4]
                            · have p488_0 := h488c.1
                              have p488_1 := h488c.2.1
                              have p488_2 := h488c.2.2.1
                              have p488_3 := h488c.2.2.2
                              linarith only [hlam, p488_0]
                      · linarith only [h370, h477, h479, h482, h483, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h370, h479, h482, h5, h7, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                · linarith only [h478, h479, h6, h7, hc34, hlam, hphi, u4elo4]
              · linarith only [h370, h477, h478, hc24, hlam, hphi, u4elo3]
            · linarith only [h4, h477, h7, hc12, hlam, hphi, ht23, ht34, u4elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h641 | h641
        · linarith only [h5, h6, h641, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h643 | h643
          · rcases m.htr 1 2 4 (by decide) (by decide) with h644 | h644
            · rcases m.htr 1 3 4 (by decide) (by decide) with h645 | h645
              · rcases m.htr 1 3 5 (by decide) (by decide) with h646 | h646
                · linarith only [h1, h6, h646, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h648 | h648
                  · linarith only [h2, h641, h648, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h650 | h650
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h651 | h651
                      · linarith only [h1, h6, h643, h651, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h653 | h653
                        · linarith only [h2, h641, h644, h653, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h655 | h655
                          · linarith only [h0, h641, h643, h650, h655, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h5, h6, h655, hc34, hlam, hphi, u4elo4]
                    · linarith only [h1, h6, h645, h650, hc23, hc35, hlam, hphi]
              · linarith only [h5, h6, h641, h645, hc13, hlam, hphi, ht34, u4elo4]
            · linarith only [h4, h641, h644, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h661 | h661
            · linarith only [h3, h6, h641, h643, h661, hc24, hlam, hphi, u4elo4]
            · linarith only [h4, h641, h661, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h664 | h664
      · rcases m.htr 0 4 5 (by decide) (by decide) with h665 | h665
        · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
          · rcases m.htr 1 2 4 (by decide) (by decide) with h667 | h667
            · rcases m.htr 1 3 4 (by decide) (by decide) with h668 | h668
              · linarith only [h1, h5, h668, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h670 | h670
                · rcases m.htr 1 4 5 (by decide) (by decide) with h671 | h671
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h672 | h672
                    · linarith only [h1, h5, h666, h672, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h674 | h674
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h675 | h675
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h676 | h676
                          · rcases h3bigk with h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c | h677c
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h5, h666, h674, h676, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p677_1, u4elo3]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h5, h674, h676, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p677_1, u4elo3]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h5, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h5, h676, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p677_1, u4elo3]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h1, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h1, h674, h676, hc01, hc45, hlam, hphi, ht0b, ht5b, p677_1]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h668, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h1, h5, h676, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p677_1, u4elo3]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h3, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h666, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h672, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h0, h667, h672, h676, hc01, hc45, hlam, hphi, ht0b, ht5b, p677_1]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [hc03, hlam, hphi, ht34, p677_1, u4elo3]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h666, hc23, hlam, hphi, ht34, p677_1, u4elo3]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, p677_1, u4elo3]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              rcases p677_3 (m.d 0 3) (by simp) with h697 | h697
                              · linarith only [h5, h697, hlam]
                              · linarith only [h664, h697, hlam]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h664, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h670, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h674, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [h676, hlam, p677_0]
                            · have p677_0 := h677c.1
                              have p677_1 := h677c.2.1
                              have p677_2 := h677c.2.2.1
                              have p677_3 := h677c.2.2.2
                              linarith only [hlam, p677_0]
                          · linarith only [h5, h676, hc03, hlam, hphi, ht34, u4elo4]
                        · linarith only [h1, h5, h670, h671, h675, hc24, hlam, hphi, u4elo3]
                      · linarith only [h5, h664, h674, hc23, hlam, hphi, ht34, u4elo3]
                  · linarith only [h5, h665, h671, hc14, hlam, hphi, u4elo3]
                · linarith only [h5, h664, h670, hc13, hlam, hphi, ht34, u4elo3]
            · linarith only [h4, h5, h666, h667, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h3, h5, h666, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · linarith only [h5, h664, h665, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h713 | h713
        · rcases m.htr 1 2 3 (by decide) (by decide) with h714 | h714
          · rcases m.htr 1 2 4 (by decide) (by decide) with h715 | h715
            · rcases m.htr 1 3 4 (by decide) (by decide) with h716 | h716
              · linarith only [h1, h5, h716, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h718 | h718
                · linarith only [h1, h664, h718, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h720 | h720
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h721 | h721
                    · linarith only [h1, h5, h714, h721, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h723 | h723
                      · linarith only [h1, h664, h714, h723, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h725 | h725
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h726 | h726
                          · rcases h3bigk with h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c | h727c
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h664, h726, hc13, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h664, h726, hc23, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h5, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h664, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h1, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h1, h664, h726, hc23, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h716, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h718, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h3, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h714, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h721, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h723, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hc03, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h714, hc23, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hc23, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h1, h664, h714, hc23, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h1, h714, h726, hc23, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h714, h726, hc23, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h726, hc23, hlam, hphi, ht34, p727_1, u4elo3]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [h726, hlam, p727_0]
                            · have p727_0 := h727c.1
                              have p727_1 := h727c.2.1
                              have p727_2 := h727c.2.2.1
                              have p727_3 := h727c.2.2.2
                              linarith only [hlam, p727_0]
                          · linarith only [h0, h5, h715, h725, h726, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h2, h720, h725, hc24, hlam, hphi, u4elo0]
                  · linarith only [h5, h713, h720, hc14, hlam, hphi, u4elo3]
            · linarith only [h4, h5, h714, h715, hc23, hlam, hphi, ht34, u4elo3]
          · linarith only [h3, h5, h714, hc12, hlam, hphi, ht23, ht34, u4elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h758 | h758
          · rcases m.htr 1 2 4 (by decide) (by decide) with h759 | h759
            · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
              · linarith only [h1, h5, h713, h760, hc34, hlam, hphi, u4elo4]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h762 | h762
                · linarith only [h1, h664, h762, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h764 | h764
                  · linarith only [h1, h5, h713, h758, h764, hc23, hlam, hphi, ht34, u4elo1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h766 | h766
                    · linarith only [h1, h5, h758, h766, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h768 | h768
                      · linarith only [h1, h664, h758, h768, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h770 | h770
                        · linarith only [h1, h5, h713, h758, h770, hc23, hlam, hphi, ht34, u4elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h772 | h772
                          · linarith only [h1, h5, h713, h758, h772, hc23, hlam, hphi, ht34, u4elo3]
                          · linarith only [h1, h5, h758, h772, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h4, h713, h759, hc12, hlam, hphi, ht23, ht34, u4elo4]
          · linarith only [h3, h5, h758, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]

end R2N4
