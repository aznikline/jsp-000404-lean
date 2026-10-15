import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3116000 in
set_option maxHeartbeats 3116000 in
theorem r1l7_21_14_H_I_L_0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1bigk := hb1.1
  have h4elo := hb4.1
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h11, h13, h5, hc01, hc45, hlam, hphi, ht0b, ht5b]
                          · linarith only [h13, h4, hc34, hlam, hphi, u4elo0]
                        · linarith only [h10, h12, h2, hc24, hlam, hphi, u4elo0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                          · rcases h1bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h11, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h17, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              rcases p19_3 (m.d 0 1) (by simp) with h24 | h24
                              · rcases p19_3 (m.d 1 2) (by simp) with h25 | h25
                                · linarith only [h0, h25, hlam]
                                · linarith only [h25, h7, hlam]
                              · linarith only [h24, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h0, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h11, h8, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h0, h11, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h1, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h5, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h11, h8, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h0, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h2, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h6, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h8, hlam, p19_1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p19_1, u4elo1]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h3, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h7, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h9, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [h10, hlam, p19_0]
                            · have p19_0 := h19c.1
                              have p19_1 := h19c.2.1
                              have p19_2 := h19c.2.2.1
                              have p19_3 := h19c.2.2.2
                              linarith only [hlam, p19_0]
                          · linarith only [h11, h18, hc23, hlam, hphi, ht34, u4elo4]
                        · linarith only [h10, h17, h2, hc24, hlam, hphi, u4elo0]
                    · linarith only [h10, h4, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                    · linarith only [h52, h8, h9, hlam]
                    · linarith only [h4, h52, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h55 | h55
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h57 | h57
                      · linarith only [h5, h57, h8, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h59 | h59
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                          · rcases h1bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h55, h60, hc01, hc45, hlam, hphi, ht0b, ht5b, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h55, h60, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              rcases p61_3 (m.d 0 1) (by simp) with h66 | h66
                              · rcases p61_3 (m.d 1 2) (by simp) with h67 | h67
                                · linarith only [h0, h67, hlam]
                                · linarith only [h67, h7, hlam]
                              · linarith only [h66, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h55, h60, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, h55, h60, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h1, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h5, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h8, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h7, h8, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p61_1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h2, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h6, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hc13, hlam, hphi, ht34, p61_1, u4elo1]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h2, h55, h60, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p61_1, u4elo0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h3, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h7, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h55, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [h56, hlam, p61_0]
                            · have p61_0 := h61c.1
                              have p61_1 := h61c.2.1
                              have p61_2 := h61c.2.2.1
                              have p61_3 := h61c.2.2.2
                              linarith only [hlam, p61_0]
                          · linarith only [h59, h60, h8, hc14, hlam, hphi, u4elo2]
                        · linarith only [h56, h57, h59, hc23, hlam, hphi, ht34, u4elo1]
                    · linarith only [h4, h56, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h95 | h95
                      · linarith only [h0, h5, h8, h95, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h97 | h97
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                          · rcases h1bigk with h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p99_1]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              rcases p99_3 (m.d 0 1) (by simp) with h102 | h102
                              · rcases p99_3 (m.d 1 2) (by simp) with h103 | h103
                                · linarith only [h0, h103, hlam]
                                · linarith only [h103, h5, hlam]
                              · linarith only [h102, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h6, h97, hc01, hc45, hlam, hphi, ht0b, ht5b, p99_1]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              rcases p99_3 (m.d 0 1) (by simp) with h108 | h108
                              · rcases p99_3 (m.d 1 2) (by simp) with h109 | h109
                                · linarith only [h0, h109, hlam]
                                · linarith only [h109, h7, hlam]
                              · linarith only [h108, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h0, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h0, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p99_1]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h0, h6, h97, hc01, hc45, hlam, hphi, ht0b, ht5b, p99_1]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h0, h5, h55, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p99_1]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h1, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h5, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h8, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h55, hlam, p99_1]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h2, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h6, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h5, hc23, hlam, hphi, ht34, p99_1, u4elo1]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h2, h5, h55, hc23, hlam, hphi, ht34, p99_1, u4elo0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h3, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h7, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h3, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p99_1]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [h94, hlam, p99_0]
                            · have p99_0 := h99c.1
                              have p99_1 := h99c.2.1
                              have p99_2 := h99c.2.2.1
                              have p99_3 := h99c.2.2.2
                              linarith only [hlam, p99_0]
                          · linarith only [h8, h97, h98, hc14, hlam, hphi, u4elo2]
                        · linarith only [h4, h95, h97, hc23, hlam, hphi, ht34, u4elo0]
                    · linarith only [h4, h94, hc14, hlam, hphi, u4elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                  · linarith only [h137, h5, h7, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                    · linarith only [h139, h6, h7, hlam]
                    · linarith only [h139, h4, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                  · linarith only [h142, h5, h7, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                    · linarith only [h144, h6, h7, hlam]
                    · linarith only [h136, h144, h4, hc13, hlam, hphi, ht34, u4elo0]
            · linarith only [h5, h6, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
            · rcases m.htr 1 2 5 (by decide) (by decide) with h149 | h149
              · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                · rcases m.htr 1 3 5 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h152 | h152
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h153 | h153
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h155 | h155
                          · rcases h1bigk with h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c | h156c
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h148, h153, h155, hc01, hc45, hlam, hphi, ht0b, ht5b, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h148, h153, h155, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h148, h153, h155, hc01, hc45, hlam, hphi, ht0b, ht5b, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              rcases p156_3 (m.d 0 1) (by simp) with h161 | h161
                              · rcases p156_3 (m.d 1 2) (by simp) with h162 | h162
                                · linarith only [h0, h162, hlam]
                                · linarith only [h149, h162, hlam]
                              · linarith only [h161, hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h0, hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h5, hlam, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h148, h153, h155, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h5, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h1, hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h1, h148, h153, h155, hc01, hc45, hlam, hphi, ht0b, ht5b, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h1, h149, hc01, hc25, hlam, hphi, ht0b, ht5b, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h2, hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h148, hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h150, hlam, p156_1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h149, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p156_1, u4elo1]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h3, hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h149, hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h151, hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [h152, hlam, p156_0]
                            · have p156_0 := h156c.1
                              have p156_1 := h156c.2.1
                              have p156_2 := h156c.2.2.1
                              have p156_3 := h156c.2.2.2
                              linarith only [hlam, p156_0]
                          · linarith only [h154, h155, hc34, hlam, hphi, u4elo2]
                        · linarith only [h152, h154, h2, hc24, hlam, hphi, u4elo0]
                      · linarith only [h153, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h148, h152, h4, hc24, hlam, hphi, u4elo0]
                  · linarith only [h149, h151, h5, hlam]
                · linarith only [h148, h150, h5, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h194 | h194
                    · linarith only [h148, h149, h194, hlam]
                    · linarith only [h194, h4, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h197 | h197
                    · linarith only [h148, h193, h197, h5, hlam]
                    · linarith only [h197, h4, hc14, hlam, hphi, u4elo0]
                · linarith only [h148, h192, h5, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
              · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
                · rcases m.htr 1 3 5 (by decide) (by decide) with h203 | h203
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h204 | h204
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h207 | h207
                          · rcases h1bigk with h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c | h208c
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h201, h206, hc01, hc45, hlam, hphi, ht0b, ht5b, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h202, h207, hc01, hc45, hlam, hphi, ht0b, ht5b, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h148, h201, h206, hc01, hc45, hlam, hphi, ht0b, ht5b, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              rcases p208_3 (m.d 0 1) (by simp) with h213 | h213
                              · rcases p208_3 (m.d 1 2) (by simp) with h214 | h214
                                · linarith only [h0, h214, hlam]
                                · linarith only [h201, h214, hlam]
                              · linarith only [h213, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h0, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h5, hlam, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h148, hlam, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h148, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p208_1, u4elo2]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h1, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h201, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h1, h148, h201, h206, hc01, hc45, hlam, hphi, ht0b, ht5b, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h1, h201, h206, hc01, hc45, hlam, hphi, ht0b, ht5b, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h2, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h201, h206, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h202, hlam, p208_1]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h2, h201, h206, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p208_1, u4elo0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h3, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h201, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h203, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [h204, hlam, p208_0]
                            · have p208_0 := h208c.1
                              have p208_1 := h208c.2.1
                              have p208_2 := h208c.2.2.1
                              have p208_3 := h208c.2.2.2
                              linarith only [hlam, p208_0]
                          · linarith only [h207, h4, hc34, hlam, hphi, u4elo0]
                        · linarith only [h148, h206, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h205, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h204, h4, hc14, hlam, hphi, u4elo0]
                  · linarith only [h201, h203, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h244 | h244
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h245 | h245
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h247 | h247
                          · rcases h1bigk with h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c | h248c
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h201, hc01, hc25, hlam, hphi, ht0b, ht5b, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h201, h246, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h201, h202, h246, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              rcases p248_3 (m.d 0 1) (by simp) with h253 | h253
                              · rcases p248_3 (m.d 1 2) (by simp) with h254 | h254
                                · linarith only [h0, h254, hlam]
                                · linarith only [h201, h254, hlam]
                              · linarith only [h253, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h0, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h5, hlam, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h148, hlam, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h202, h245, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p248_1, u4elo2]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h1, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h202, h245, hc12, hlam, hphi, ht23, ht34, p248_1, u4elo2]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h202, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h201, h202, h245, h246, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p248_1, u4elo2]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h2, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h201, h246, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p248_1]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h202, h245, hc13, hlam, hphi, ht34, p248_1, u4elo2]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h201, h202, h245, h246, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p248_1, u4elo2]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h3, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h201, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h243, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [h244, hlam, p248_0]
                            · have p248_0 := h248c.1
                              have p248_1 := h248c.2.1
                              have p248_2 := h248c.2.2.1
                              have p248_3 := h248c.2.2.2
                              linarith only [hlam, p248_0]
                          · linarith only [h202, h247, h4, hc14, hlam, hphi, u4elo0]
                        · linarith only [h202, h245, h246, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h201, h245, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h201, h202, h244, h4, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo0]
                  · linarith only [h201, h243, h5, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h283 | h283
                · rcases m.htr 1 3 5 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h285 | h285
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h286 | h286
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h287 | h287
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h288 | h288
                          · rcases h1bigk with h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c | h289c
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              rcases p289_3 (m.d 0 1) (by simp) with h291 | h291
                              · rcases p289_3 (m.d 1 2) (by simp) with h292 | h292
                                · linarith only [h292, hlam, p289_0]
                                · rcases p289_3 (m.d 1 3) (by simp) with h294 | h294
                                  · linarith only [h1, h294, hlam]
                                  · linarith only [h294, h5, hlam]
                              · linarith only [h291, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h283, h288, hc01, hc45, hlam, hphi, ht0b, ht5b, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h283, h288, hc01, hc45, hlam, hphi, ht0b, ht5b, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              rcases p289_3 (m.d 0 1) (by simp) with h300 | h300
                              · rcases p289_3 (m.d 1 2) (by simp) with h301 | h301
                                · linarith only [h0, h301, hlam]
                                · rcases p289_3 (m.d 1 3) (by simp) with h303 | h303
                                  · linarith only [h1, h303, hlam]
                                  · linarith only [h284, h303, hlam]
                              · linarith only [h300, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h0, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h5, hlam, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h148, hlam, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h201, hlam, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h1, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h1, h283, h288, hc01, hc45, hlam, hphi, ht0b, ht5b, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h1, hc01, hc15, hlam, hphi, ht0b, ht5b, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h2, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p289_1, u4elo1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h283, hlam, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h2, h201, hc12, hlam, hphi, ht23, ht34, p289_1, u4elo0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h3, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p289_1]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h284, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [h285, hlam, p289_0]
                            · have p289_0 := h289c.1
                              have p289_1 := h289c.2.1
                              have p289_2 := h289c.2.2.1
                              have p289_3 := h289c.2.2.2
                              linarith only [hlam, p289_0]
                          · linarith only [h288, h4, hc34, hlam, hphi, u4elo0]
                        · linarith only [h2, h285, h287, hc24, hlam, hphi, u4elo0]
                      · linarith only [h286, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h285, h4, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h331 | h331
                    · linarith only [h283, h284, h331, hlam]
                    · linarith only [h331, h4, hc14, hlam, hphi, u4elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h334 | h334
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h335 | h335
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h337 | h337
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h338 | h338
                          · rcases h1bigk with h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c | h339c
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              rcases p339_3 (m.d 0 1) (by simp) with h341 | h341
                              · rcases p339_3 (m.d 1 2) (by simp) with h342 | h342
                                · linarith only [h342, hlam, p339_0]
                                · rcases p339_3 (m.d 1 3) (by simp) with h344 | h344
                                  · linarith only [h1, h344, hlam]
                                  · linarith only [h344, h5, hlam]
                              · linarith only [h341, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h334, h338, hc01, hc45, hlam, hphi, ht0b, ht5b, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h283, h334, h338, hc01, hc45, hlam, hphi, ht0b, ht5b, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              rcases p339_3 (m.d 0 1) (by simp) with h350 | h350
                              · rcases p339_3 (m.d 1 2) (by simp) with h351 | h351
                                · linarith only [h0, h351, hlam]
                                · rcases p339_3 (m.d 1 3) (by simp) with h353 | h353
                                  · linarith only [h1, h353, hlam]
                                  · linarith only [h334, h353, hlam]
                              · linarith only [h350, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h0, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h5, hlam, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h148, hlam, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h201, hlam, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h1, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h283, h336, hc12, hlam, hphi, ht23, ht34, p339_1, u4elo2]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h283, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h283, h336, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p339_1, u4elo2]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h2, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p339_1, u4elo1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h283, h336, hc13, hlam, hphi, ht34, p339_1, u4elo2]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h201, h283, h336, hc12, hlam, hphi, ht23, ht34, p339_1, u4elo2]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h3, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p339_1]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h334, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [h335, hlam, p339_0]
                            · have p339_0 := h339c.1
                              have p339_1 := h339c.2.1
                              have p339_2 := h339c.2.2.1
                              have p339_3 := h339c.2.2.2
                              linarith only [hlam, p339_0]
                          · linarith only [h283, h334, h338, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h283, h334, h335, h337, hc24, hlam, hphi, u4elo3]
                      · linarith only [h336, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h335, h4, hc14, hlam, hphi, u4elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h381 | h381
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h382 | h382
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h384 | h384
                          · rcases h1bigk with h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c | h385c
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              rcases p385_3 (m.d 0 1) (by simp) with h387 | h387
                              · rcases p385_3 (m.d 1 2) (by simp) with h388 | h388
                                · linarith only [h388, hlam, p385_0]
                                · rcases p385_3 (m.d 1 3) (by simp) with h390 | h390
                                  · linarith only [h1, h390, hlam]
                                  · linarith only [h390, h5, hlam]
                              · linarith only [h387, hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              rcases p385_3 (m.d 0 1) (by simp) with h394 | h394
                              · rcases p385_3 (m.d 1 2) (by simp) with h395 | h395
                                · linarith only [h0, h395, hlam]
                                · rcases p385_3 (m.d 1 3) (by simp) with h397 | h397
                                  · linarith only [h397, hlam, p385_0]
                                  · rcases p385_3 (m.d 1 4) (by simp) with h399 | h399
                                    · linarith only [h2, h399, hlam]
                                    · linarith only [h283, h399, hlam]
                              · linarith only [h394, hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h381, hc01, hc45, hlam, hphi, ht0b, ht5b, p385_1]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              rcases p385_3 (m.d 0 1) (by simp) with h404 | h404
                              · rcases p385_3 (m.d 1 2) (by simp) with h405 | h405
                                · linarith only [h0, h405, hlam]
                                · rcases p385_3 (m.d 1 3) (by simp) with h407 | h407
                                  · linarith only [h1, h407, hlam]
                                  · rcases p385_3 (m.d 1 4) (by simp) with h409 | h409
                                    · linarith only [h2, h409, hlam]
                                    · linarith only [h381, h409, hlam]
                              · linarith only [h404, hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h0, hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h5, hlam, p385_1]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h148, hlam, p385_1]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h201, hlam, p385_1]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h1, hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h334, hc12, hc35, hlam, hphi, ht23, p385_1]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h283, hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h334, hlam, p385_1]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h2, hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [hc12, hlam, hphi, ht23, ht34, p385_1, u4elo1]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h283, h382, hc13, hlam, hphi, ht34, p385_1, u4elo2]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h283, h382, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p385_1, u4elo2]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h3, hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p385_1]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h3, h4, h5, hc12, hlam, hphi, ht23, ht34, p385_1, u4elo0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [h381, hlam, p385_0]
                            · have p385_0 := h385c.1
                              have p385_1 := h385c.2.1
                              have p385_2 := h385c.2.2.1
                              have p385_3 := h385c.2.2.2
                              linarith only [hlam, p385_0]
                          · linarith only [h283, h384, h4, hc14, hlam, hphi, u4elo0]
                        · linarith only [h283, h382, h383, h5, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h382, h5, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h381, h4, hc14, hlam, hphi, u4elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
          · rcases m.htr 1 2 4 (by decide) (by decide) with h438 | h438
            · rcases m.htr 1 2 5 (by decide) (by decide) with h439 | h439
              · rcases m.htr 1 3 4 (by decide) (by decide) with h440 | h440
                · rcases m.htr 1 3 5 (by decide) (by decide) with h441 | h441
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h442 | h442
                    · linarith only [h4, h442, hc04, hlam, hphi, u4elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h444 | h444
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h445 | h445
                        · linarith only [h2, h4, h438, h445, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h447 | h447
                          · linarith only [h4, h437, h444, h447, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h1bigk with h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h437, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h441, hc01, hc35, hlam, hphi, ht0b, ht5b, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              rcases p449_3 (m.d 0 1) (by simp) with h453 | h453
                              · rcases p449_3 (m.d 1 2) (by simp) with h454 | h454
                                · linarith only [h0, h454, hlam]
                                · linarith only [h438, h454, hlam]
                              · linarith only [h453, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              rcases p449_3 (m.d 0 1) (by simp) with h458 | h458
                              · rcases p449_3 (m.d 1 2) (by simp) with h459 | h459
                                · linarith only [h0, h459, hlam]
                                · linarith only [h439, h459, hlam]
                              · linarith only [h458, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h437, h444, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, h438, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, h438, h442, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h1, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h437, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h1, h438, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, h437, h438, h442, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h2, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h438, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h440, hlam, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h442, hlam, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h3, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h439, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h441, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h3, h438, h444, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                      · linarith only [h2, h4, h440, h444, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h484 | h484
                    · linarith only [h2, h4, h484, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h486 | h486
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h487 | h487
                        · linarith only [h4, h487, hc04, hlam, hphi, u4elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h489 | h489
                          · linarith only [h3, h4, h437, h441, h486, h489, hlam]
                          · linarith only [h437, h441, h486, h489, hc34, hlam, hphi, u4elo4]
                      · linarith only [h440, h441, h486, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h493 | h493
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h494 | h494
                    · linarith only [h2, h4, h494, hlam]
                    · linarith only [h440, h493, h494, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h497 | h497
                    · linarith only [h2, h4, h497, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h499 | h499
                      · linarith only [h437, h440, h499, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h501 | h501
                        · linarith only [h4, h501, hc04, hlam, hphi, u4elo2]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h503 | h503
                          · linarith only [h2, h4, h437, h440, h503, hc23, hlam, hphi, ht34, u4elo3]
                          · linarith only [h437, h440, h503, hc23, hlam, hphi, ht34, u4elo4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h506 | h506
                · rcases m.htr 1 3 5 (by decide) (by decide) with h507 | h507
                  · linarith only [h437, h439, h507, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h509 | h509
                    · linarith only [h2, h4, h509, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h511 | h511
                      · linarith only [h3, h4, h437, h439, h511, hc34, hlam, hphi, u4elo4]
                      · linarith only [h3, h4, h437, h439, h506, h511, hc23, hlam, hphi, ht34, u4elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h514 | h514
                  · linarith only [h2, h4, h437, h439, h506, h514, hc23, hlam, hphi, ht34, u4elo4]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h516 | h516
                    · linarith only [h2, h4, h516, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h518 | h518
                      · linarith only [h3, h4, h437, h439, h518, hc34, hlam, hphi, u4elo4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h520 | h520
                        · linarith only [h3, h4, h438, h439, h520, hlam]
                        · linarith only [h438, h439, h518, h520, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h437, h438, hc23, hlam, hphi, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
            · rcases m.htr 1 2 5 (by decide) (by decide) with h525 | h525
              · rcases m.htr 1 3 4 (by decide) (by decide) with h526 | h526
                · rcases m.htr 1 3 5 (by decide) (by decide) with h527 | h527
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h528 | h528
                    · linarith only [h2, h4, h528, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h530 | h530
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h531 | h531
                        · linarith only [h2, h4, h437, h524, h531, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h533 | h533
                          · linarith only [h2, h4, h524, h530, h533, hlam]
                          · rcases h1bigk with h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c | h535c
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h524, h530, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h437, h524, h530, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              rcases p535_3 (m.d 0 1) (by simp) with h539 | h539
                              · rcases p535_3 (m.d 1 2) (by simp) with h540 | h540
                                · linarith only [h0, h540, hlam]
                                · linarith only [h524, h540, hlam]
                              · linarith only [h539, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              rcases p535_3 (m.d 0 1) (by simp) with h544 | h544
                              · rcases p535_3 (m.d 1 2) (by simp) with h545 | h545
                                · linarith only [h0, h545, hlam]
                                · linarith only [h525, h545, hlam]
                              · linarith only [h544, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h0, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h437, hlam, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h0, h524, h530, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h437, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h1, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h1, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h1, h524, h530, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h1, h525, h530, h531, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h2, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h524, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h526, hlam, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h528, hlam, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h3, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h525, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h527, hlam, p535_0]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [h3, h524, h530, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p535_1]
                            · have p535_0 := h535c.1
                              have p535_1 := h535c.2.1
                              have p535_2 := h535c.2.2.1
                              have p535_3 := h535c.2.2.2
                              linarith only [hlam, p535_0]
                      · linarith only [h437, h530, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · linarith only [h437, h525, h527, hlam]
                · linarith only [h437, h524, h526, hc24, hlam, hphi, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h572 | h572
                · rcases m.htr 1 3 5 (by decide) (by decide) with h573 | h573
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
                    · linarith only [h2, h3, h4, h524, h525, h574, hc24, hlam, hphi, u4elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h576 | h576
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h577 | h577
                        · linarith only [h2, h4, h437, h524, h577, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h524, h525, h576, h577, hc34, hlam, hphi, u4elo4]
                      · linarith only [h437, h576, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h581 | h581
                    · linarith only [h2, h4, h581, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h583 | h583
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h584 | h584
                        · linarith only [h2, h4, h437, h524, h584, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h524, h525, h583, h584, hc34, hlam, hphi, u4elo4]
                      · linarith only [h437, h583, hc12, hlam, hphi, ht23, ht34, u4elo3]
                · linarith only [h437, h524, h572, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h589 | h589
              · rcases m.htr 1 3 4 (by decide) (by decide) with h590 | h590
                · rcases m.htr 1 3 5 (by decide) (by decide) with h591 | h591
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h592 | h592
                    · linarith only [h2, h4, h592, hlam]
                    · linarith only [h524, h589, h592, hlam]
                  · linarith only [h2, h4, h524, h589, h590, h591, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h596 | h596
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h597 | h597
                    · linarith only [h2, h4, h597, hlam]
                    · linarith only [h437, h589, h590, h597, hlam]
                  · linarith only [h437, h589, h596, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h601 | h601
                · rcases m.htr 1 3 5 (by decide) (by decide) with h602 | h602
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h603 | h603
                    · linarith only [h2, h4, h603, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h605 | h605
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h606 | h606
                        · linarith only [h4, h606, hc04, hlam, hphi, u4elo2]
                        · linarith only [h524, h606, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h437, h605, hc12, hlam, hphi, ht23, ht34, u4elo3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h610 | h610
                    · linarith only [h2, h4, h610, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h612 | h612
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h613 | h613
                        · linarith only [h4, h613, hc04, hlam, hphi, u4elo2]
                        · linarith only [h524, h613, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h437, h589, h601, h602, h612, hc12, hc25, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h617 | h617
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h618 | h618
                    · linarith only [h2, h4, h618, hlam]
                    · linarith only [h601, h617, h618, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h621 | h621
                    · linarith only [h2, h4, h621, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h623 | h623
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h624 | h624
                        · linarith only [h4, h624, hc04, hlam, hphi, u4elo2]
                        · linarith only [h524, h624, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h437, h623, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h628 | h628
        · linarith only [h2, h3, h628, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
          · linarith only [h0, h3, h628, h630, hc23, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h632 | h632
            · linarith only [h1, h3, h628, h630, h632, hc24, hlam, hphi, u4elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h634 | h634
              · linarith only [h1, h3, h630, h634, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h636 | h636
                · linarith only [h1, h3, h628, h636, hc34, hlam, hphi, u4elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h638 | h638
                  · linarith only [h2, h3, h636, h638, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h640 | h640
                    · linarith only [h2, h3, h628, h640, hlam]
                    · linarith only [h2, h3, h630, h636, h640, hc12, hlam, hphi, ht23, ht34, u4elo4]
    · linarith only [h0, h2, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h644 | h644
    · rcases m.htr 0 1 5 (by decide) (by decide) with h645 | h645
      · rcases m.htr 0 4 5 (by decide) (by decide) with h646 | h646
        · rcases m.htr 1 2 3 (by decide) (by decide) with h647 | h647
          · linarith only [h0, h1, h647, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h649 | h649
            · rcases m.htr 1 2 5 (by decide) (by decide) with h650 | h650
              · rcases m.htr 1 3 4 (by decide) (by decide) with h651 | h651
                · rcases m.htr 1 3 5 (by decide) (by decide) with h652 | h652
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h653 | h653
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h654 | h654
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h655 | h655
                        · linarith only [h0, h1, h649, h655, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h644, h653, h654, h655, hc34, hlam, hphi, u4elo0]
                      · linarith only [h0, h1, h647, h654, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h646, h653, hc14, hlam, hphi, u4elo0]
                  · linarith only [h0, h1, h649, h652, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h649, h651, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h662 | h662
                · rcases m.htr 1 3 5 (by decide) (by decide) with h663 | h663
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h664 | h664
                    · linarith only [h649, h650, h664, hlam]
                    · linarith only [h646, h664, hc14, hlam, hphi, u4elo0]
                  · linarith only [h1, h645, h649, h650, h663, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1, h645, h649, h650, h662, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h669 | h669
              · rcases m.htr 1 3 4 (by decide) (by decide) with h670 | h670
                · rcases m.htr 1 3 5 (by decide) (by decide) with h671 | h671
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h672 | h672
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h673 | h673
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h674 | h674
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h675 | h675
                          · rcases h1bigk with h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c | h676c
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h669, h674, hc01, hc45, hlam, hphi, ht0b, ht5b, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h1, hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h1, h647, h649, h669, h674, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h1, h647, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h0, hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h647, hlam, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h649, hlam, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h649, h671, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p676_1, u4elo2]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h647, hc01, hc23, hlam, hphi, ht12, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h647, hc12, hc23, hlam, hphi, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h647, h649, h669, h674, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              rcases p676_3 (m.d 0 1) (by simp) with h691 | h691
                              · linarith only [h1, h691, hlam]
                              · linarith only [h645, h691, hlam]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h644, hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h644, h669, h674, hc01, hc45, hlam, hphi, ht0b, ht5b, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h670, hlam, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h1, h644, h647, h669, h674, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p676_1]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h645, hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h669, hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h671, hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [h672, hlam, p676_0]
                            · have p676_0 := h676c.1
                              have p676_1 := h676c.2.1
                              have p676_2 := h676c.2.2.1
                              have p676_3 := h676c.2.2.2
                              linarith only [hlam, p676_0]
                          · linarith only [h0, h1, h647, h669, h674, h675, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1, h644, h647, h649, h672, h674, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h644, h647, h672, h673, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1, h644, h646, h649, h669, h672, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h1, h669, h671, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                · linarith only [h1, h644, h649, h669, h670, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h710 | h710
                · rcases m.htr 1 3 5 (by decide) (by decide) with h711 | h711
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h712 | h712
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h713 | h713
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h714 | h714
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h715 | h715
                          · rcases h1bigk with h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c | h716c
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h1, hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h1, h710, h715, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h1, h669, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h0, hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h647, hlam, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h649, hlam, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h669, hlam, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h647, hc12, hc23, hlam, hphi, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h647, h710, h715, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h647, h669, hc12, hc23, hlam, hphi, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h644, hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h644, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h710, hlam, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h1, h644, h647, h669, hc12, hc23, hlam, hphi, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h645, hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h1, h645, h647, hc12, hc23, hlam, hphi, p716_1]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h711, hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [h712, hlam, p716_0]
                            · have p716_0 := h716c.1
                              have p716_1 := h716c.2.1
                              have p716_2 := h716c.2.2.1
                              have p716_3 := h716c.2.2.2
                              linarith only [hlam, p716_0]
                          · linarith only [h646, h715, hc34, hlam, hphi, u4elo0]
                        · linarith only [h1, h644, h647, h712, h714, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1, h644, h647, h712, h713, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h1, h644, h646, h647, h649, h712, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h711, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h644, h649, h710, hc12, hc34, hlam, hphi, ht23]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h748 | h748
          · linarith only [h0, h1, h748, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h750 | h750
            · rcases m.htr 1 2 5 (by decide) (by decide) with h751 | h751
              · rcases m.htr 1 3 4 (by decide) (by decide) with h752 | h752
                · rcases m.htr 1 3 5 (by decide) (by decide) with h753 | h753
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h754 | h754
                    · linarith only [h644, h646, h754, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h756 | h756
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h757 | h757
                        · linarith only [h0, h646, h750, h757, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h759 | h759
                          · linarith only [h644, h646, h750, h756, h759, hlam]
                          · rcases h1bigk with h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c | h761c
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h1, h748, hc12, hc23, hlam, hphi, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h1, hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h1, h748, h750, h756, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h1, h748, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h0, hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h748, hlam, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h0, h1, h748, h750, h756, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h0, h1, h748, h751, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h748, hc01, hc23, hlam, hphi, ht12, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h748, hc12, hc23, hlam, hphi, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              rcases p761_3 (m.d 0 1) (by simp) with h775 | h775
                              · linarith only [h1, h775, hlam]
                              · linarith only [h644, h775, hlam]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              rcases p761_3 (m.d 0 1) (by simp) with h778 | h778
                              · linarith only [h1, h778, hlam]
                              · linarith only [h645, h778, hlam]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h644, hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h750, hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h752, hlam, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h754, hlam, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h645, hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h751, hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h753, hlam, p761_0]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [h645, h750, h756, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p761_1]
                            · have p761_0 := h761c.1
                              have p761_1 := h761c.2.1
                              have p761_2 := h761c.2.2.1
                              have p761_3 := h761c.2.2.2
                              linarith only [hlam, p761_0]
                      · linarith only [h0, h1, h748, h756, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h0, h1, h750, h753, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h750, h752, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h794 | h794
                · rcases m.htr 1 3 5 (by decide) (by decide) with h795 | h795
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h796 | h796
                    · linarith only [h644, h646, h796, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h798 | h798
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h799 | h799
                        · linarith only [h645, h646, h750, h751, h799, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h750, h751, h798, h799, hc34, hlam, hphi, u4elo4]
                      · linarith only [h1, h645, h748, h750, h751, h798, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h1, h645, h750, h751, h795, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1, h645, h750, h751, h794, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h805 | h805
              · rcases m.htr 1 3 4 (by decide) (by decide) with h806 | h806
                · rcases m.htr 1 3 5 (by decide) (by decide) with h807 | h807
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h808 | h808
                    · linarith only [h644, h646, h808, hlam]
                    · linarith only [h750, h805, h808, hlam]
                  · linarith only [h1, h644, h750, h807, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h644, h750, h805, h806, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h813 | h813
                · rcases m.htr 1 3 5 (by decide) (by decide) with h814 | h814
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h815 | h815
                    · linarith only [h644, h646, h815, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h817 | h817
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h818 | h818
                        · linarith only [h646, h818, hc04, hlam, hphi, u4elo2]
                        · linarith only [h750, h818, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h1, h645, h748, h813, h815, h817, hlam]
                  · linarith only [h0, h1, h814, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h645, h805, h813, hc12, hc34, hlam, hphi, ht23]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h824 | h824
        · linarith only [h644, h645, h824, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h826 | h826
          · linarith only [h0, h645, h824, h826, hc23, hlam, hphi, ht34, u4elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h828 | h828
            · linarith only [h0, h645, h824, h828, hc24, hlam, hphi, u4elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h830 | h830
              · linarith only [h644, h645, h828, h830, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h832 | h832
                · rcases m.htr 1 3 5 (by decide) (by decide) with h833 | h833
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h834 | h834
                    · linarith only [h644, h645, h824, h834, hlam]
                    · linarith only [h644, h645, h828, h834, hc12, hlam, hphi, ht23, ht34, u4elo4]
                  · linarith only [h1, h644, h828, h833, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h644, h828, h832, hc12, hc34, hlam, hphi, ht23]
    · linarith only [h0, h644, hc12, hlam, hphi, ht23, ht34, u4elo1]

end R2N4
