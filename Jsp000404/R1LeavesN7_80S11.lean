import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_M_LI_L_0_L_0 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h4, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · linarith only [h0, h10, h4, h7, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h4, h7, h9, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
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
                          linarith only [hc12, hlam, hphi, p15_1, u2elo0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 2) (by simp) with h19 | h19
                          · rcases p15_3 (m.d 1 2) (by simp) with h20 | h20
                            · linarith only [h0, h20, hlam]
                            · linarith only [h20, h5, hlam]
                          · linarith only [h19, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 2) (by simp) with h24 | h24
                          · rcases p15_3 (m.d 1 2) (by simp) with h25 | h25
                            · linarith only [h0, h25, hlam]
                            · linarith only [h25, h6, hlam]
                          · linarith only [h24, hlam, p15_0]
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
                          linarith only [h13, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15_1, u2elo1]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 2) (by simp) with h32 | h32
                          · rcases p15_3 (m.d 1 2) (by simp) with h33 | h33
                            · rcases p15_3 (m.d 2 3) (by simp) with h34 | h34
                              · linarith only [h34, h4, hlam]
                              · linarith only [h34, h7, hlam]
                            · linarith only [h33, hlam, p15_0]
                          · linarith only [h2, h32, hlam]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          rcases p15_3 (m.d 0 2) (by simp) with h39 | h39
                          · rcases p15_3 (m.d 1 2) (by simp) with h40 | h40
                            · rcases p15_3 (m.d 2 3) (by simp) with h41 | h41
                              · linarith only [h4, h41, hlam]
                              · linarith only [h41, h8, hlam]
                            · linarith only [h40, hlam, p15_0]
                          · linarith only [h3, h39, hlam]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h4, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h1, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15_1, u2elo0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h0, h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p15_1, u2elo0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h2, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h5, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h7, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h9, hlam, p15_0]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [h3, hlam, p15_0]
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
                          linarith only [h7, hc34, hlam, hphi, ht45, p15_1, u5elo2]
                        · have p15_0 := h15c.1
                          have p15_1 := h15c.2.1
                          have p15_2 := h15c.2.2.1
                          have p15_3 := h15c.2.2.2
                          linarith only [hlam, p15_0]
                  · linarith only [h7, h8, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h62 | h62
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h63 | h63
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h64 | h64
                      · rcases h2bigk with h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c | h65c
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hc12, hlam, hphi, p65_1, u2elo0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h62, h64, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h62, h64, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          rcases p65_3 (m.d 0 2) (by simp) with h70 | h70
                          · rcases p65_3 (m.d 1 2) (by simp) with h71 | h71
                            · linarith only [h0, h71, hlam]
                            · linarith only [h6, h71, hlam]
                          · linarith only [h70, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h0, hlam, p65_1]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h62, h64, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo1]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h0, h62, h64, h7, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          rcases p65_3 (m.d 0 2) (by simp) with h79 | h79
                          · rcases p65_3 (m.d 1 2) (by simp) with h80 | h80
                            · rcases p65_3 (m.d 2 3) (by simp) with h81 | h81
                              · linarith only [h4, h81, hlam]
                              · linarith only [h62, h81, hlam]
                            · linarith only [h80, hlam, p65_0]
                          · linarith only [h3, h79, hlam]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h1, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h4, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h7, hlam, p65_1]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p65_1, u3elo3]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h2, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h5, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p65_1, u2elo0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h0, h5, h62, h64, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p65_1, u2elo0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h3, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h6, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h62, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h63, hlam, p65_1]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hlam, p65_0]
                      · linarith only [h64, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h62, h63, h7, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h104 | h104
                      · rcases h2bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hc12, hlam, hphi, p105_1, u2elo0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          rcases p105_3 (m.d 0 2) (by simp) with h108 | h108
                          · rcases p105_3 (m.d 1 2) (by simp) with h109 | h109
                            · linarith only [h0, h109, hlam]
                            · linarith only [h109, h4, hlam]
                          · linarith only [h108, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h103, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p105_1, u2elo0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          rcases p105_3 (m.d 0 2) (by simp) with h114 | h114
                          · rcases p105_3 (m.d 1 2) (by simp) with h115 | h115
                            · linarith only [h0, h115, hlam]
                            · linarith only [h115, h6, hlam]
                          · linarith only [h114, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h0, hlam, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          rcases p105_3 (m.d 0 2) (by simp) with h121 | h121
                          · rcases p105_3 (m.d 1 2) (by simp) with h122 | h122
                            · rcases p105_3 (m.d 2 3) (by simp) with h123 | h123
                              · linarith only [h123, hlam, p105_0]
                              · rcases p105_3 (m.d 2 4) (by simp) with h125 | h125
                                · linarith only [h125, h5, hlam]
                                · linarith only [h125, h7, hlam]
                            · linarith only [h122, hlam, p105_0]
                          · linarith only [h1, h121, hlam]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h103, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p105_1, u2elo1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          rcases p105_3 (m.d 0 2) (by simp) with h131 | h131
                          · rcases p105_3 (m.d 1 2) (by simp) with h132 | h132
                            · rcases p105_3 (m.d 2 3) (by simp) with h133 | h133
                              · linarith only [h133, h4, hlam]
                              · rcases p105_3 (m.d 2 4) (by simp) with h135 | h135
                                · linarith only [h135, h5, hlam]
                                · linarith only [h103, h135, hlam]
                            · linarith only [h132, hlam, p105_0]
                          · linarith only [h131, h3, hlam]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h1, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h4, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h7, hlam, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h62, hlam, p105_1]
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
                          linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p105_1, u2elo0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h0, h5, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p105_1, u2elo0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h3, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h6, hlam, p105_0]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hc23, hlam, hphi, ht34, ht45, p105_1, u5elo2]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [h103, hlam, p105_1]
                        · have p105_0 := h105c.1
                          have p105_1 := h105c.2.1
                          have p105_2 := h105c.2.2.1
                          have p105_3 := h105c.2.2.2
                          linarith only [hlam, p105_0]
                      · linarith only [h104, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                      · linarith only [h103, h156, h7, hc23, hlam, hphi, u3elo3]
                      · linarith only [h156, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h3, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h2, h4, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
          · linarith only [h1, h4, hc12, hlam, hphi, u2elo0]
        · linarith only [h1, h3, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h163 | h163
        · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
          · rcases m.htr 1 2 4 (by decide) (by decide) with h165 | h165
            · linarith only [h0, h165, h2, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h167 | h167
              · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                · linarith only [h0, h164, h168, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                · linarith only [h0, h164, h168, h2, hc23, hlam, hphi, u3elo3]
              · linarith only [h164, h167, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h1, h164, h2, hc12, hlam, hphi, u2elo3]
        · linarith only [h1, h163, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h174 | h174
      · rcases m.htr 0 2 5 (by decide) (by decide) with h175 | h175
        · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
          · linarith only [h1, h174, h176, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
            · rcases m.htr 1 2 5 (by decide) (by decide) with h179 | h179
              · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                · rcases m.htr 2 3 5 (by decide) (by decide) with h181 | h181
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h182 | h182
                    · linarith only [h0, h1, h178, h182, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h184 | h184
                      · linarith only [h180, h182, h184, hlam]
                      · rcases h2bigk with h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c | h186c
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h1, h179, h180, h182, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p186_1, u3elo2]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h1, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h1, h180, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p186_1, u3elo2]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h1, h180, h182, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p186_1, u3elo2]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h0, hlam, p186_1]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h176, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h0, h1, h180, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p186_1, u3elo2]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h0, h1, h180, h182, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p186_1, u3elo2]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p186_1, u3elo2]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, p186_1, u3elo2]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          rcases p186_3 (m.d 0 2) (by simp) with h200 | h200
                          · linarith only [h1, h200, hlam]
                          · linarith only [h174, h200, hlam]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          rcases p186_3 (m.d 0 2) (by simp) with h203 | h203
                          · linarith only [h1, h203, hlam]
                          · linarith only [h175, h203, hlam]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h174, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h178, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h180, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h182, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h175, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h179, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h181, hlam, p186_0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [h0, h179, h180, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p186_1, u2elo0]
                        · have p186_0 := h186c.1
                          have p186_1 := h186c.2.1
                          have p186_2 := h186c.2.2.1
                          have p186_3 := h186c.2.2.2
                          linarith only [hlam, p186_0]
                  · linarith only [h1, h181, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h178, h180, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
              · linarith only [h178, h179, hc24, hlam, hphi, ht45, u5elo2]
            · linarith only [h1, h174, h178, hc12, hlam, hphi, ht23, u3elo2]
        · linarith only [h174, h175, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h221 | h221
        · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
          · linarith only [h0, h1, h222, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h224 | h224
            · linarith only [h0, h174, h224, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
              · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                · rcases m.htr 2 3 5 (by decide) (by decide) with h228 | h228
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h229 | h229
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h230 | h230
                      · rcases h2bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h174, h227, hc12, hlam, hphi, ht23, p231_1, u3elo2]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h1, hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h174, hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h174, h227, h228, h230, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p231_1, u3elo2]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h0, hlam, p231_1]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h222, hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h224, hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h0, h174, h227, h228, h230, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p231_1, u3elo2]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p231_1, u3elo2]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, p231_1, u3elo2]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h174, h221, h228, h230, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p231_1, u3elo2]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          rcases p231_3 (m.d 0 2) (by simp) with h246 | h246
                          · linarith only [h1, h246, hlam]
                          · linarith only [h221, h246, hlam]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h0, h226, h228, h230, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p231_1, u2elo3]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h226, h228, h230, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p231_1, u2elo3]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h227, hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          rcases p231_3 (m.d 0 2) (by simp) with h253 | h253
                          · linarith only [h174, h253, hlam]
                          · linarith only [h221, h253, hlam]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h221, hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h226, hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h228, hlam, p231_0]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [h229, hlam, p231_1]
                        · have p231_0 := h231c.1
                          have p231_1 := h231c.2.1
                          have p231_2 := h231c.2.2.1
                          have p231_3 := h231c.2.2.2
                          linarith only [hlam, p231_0]
                      · linarith only [h0, h174, h226, h227, h229, h230, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                    · linarith only [h174, h229, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h174, h226, h227, h228, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                · linarith only [h0, h1, h226, h227, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
              · linarith only [h1, h221, h226, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h266 | h266
          · linarith only [h0, h221, h266, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h268 | h268
            · linarith only [h0, h174, h268, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h270 | h270
              · linarith only [h0, h221, h270, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h272 | h272
                · rcases m.htr 2 3 5 (by decide) (by decide) with h273 | h273
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h274 | h274
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h275 | h275
                      · rcases h2bigk with h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c | h276c
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h221, hc12, hlam, hphi, ht23, ht34, ht45, p276_1, u5elo2]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h1, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h174, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h221, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h0, hlam, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h266, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h268, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h270, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hc02, hlam, hphi, p276_1, u2elo2]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, p276_1, u3elo2]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h0, h174, hc12, hlam, hphi, ht23, p276_1, u3elo2]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h0, h221, hc12, hlam, hphi, ht23, p276_1, u3elo2]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, p276_1, u2elo3]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hc12, hlam, hphi, p276_1, u2elo3]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h272, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h0, h221, h272, hc12, hlam, hphi, ht23, p276_1, u3elo2]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, p276_1, u2elo4]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p276_1, u5elo2]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h273, hlam, p276_0]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [h274, hlam, p276_1]
                        · have p276_0 := h276c.1
                          have p276_1 := h276c.2.1
                          have p276_2 := h276c.2.2.1
                          have p276_3 := h276c.2.2.2
                          linarith only [hlam, p276_0]
                      · rcases h2bigk with h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c | h302c
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hc12, hlam, hphi, p302_1, u2elo0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h1, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h174, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h221, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h0, hlam, p302_1]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h266, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h268, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h270, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hc02, hlam, hphi, ht23, p302_1, u3elo2]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, p302_1, u3elo2]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h274, h275, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p302_1, u3elo2]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h0, h221, hc12, hlam, hphi, ht23, p302_1, u3elo2]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, p302_1, u2elo3]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hc12, hlam, hphi, p302_1, u2elo3]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h272, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h0, h221, h272, hc12, hlam, hphi, ht23, p302_1, u3elo2]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h0, hc12, hlam, hphi, p302_1, u2elo4]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p302_1, u5elo2]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h273, hlam, p302_0]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [h274, hlam, p302_1]
                        · have p302_0 := h302c.1
                          have p302_1 := h302c.2.1
                          have p302_2 := h302c.2.2.1
                          have p302_3 := h302c.2.2.2
                          linarith only [hlam, p302_0]
                    · linarith only [h0, h174, h274, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h0, h1, h273, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                · linarith only [h0, h1, h272, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h331 | h331
    · rcases m.htr 0 2 4 (by decide) (by decide) with h332 | h332
      · rcases m.htr 0 2 5 (by decide) (by decide) with h333 | h333
        · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
          · rcases m.htr 1 2 4 (by decide) (by decide) with h335 | h335
            · rcases m.htr 1 2 5 (by decide) (by decide) with h336 | h336
              · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h339 | h339
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h340 | h340
                      · linarith only [h331, h337, h340, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                      · linarith only [h0, h331, h337, h339, h340, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h343 | h343
                      · linarith only [h0, h331, h337, h339, h343, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · rcases h2bigk with h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c | h345c
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h0, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h0, h338, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p345_1, u2elo1]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          rcases p345_3 (m.d 0 2) (by simp) with h349 | h349
                          · rcases p345_3 (m.d 1 2) (by simp) with h350 | h350
                            · rcases p345_3 (m.d 2 3) (by simp) with h351 | h351
                              · linarith only [h331, h351, hlam]
                              · linarith only [h337, h351, hlam]
                            · linarith only [h335, h350, hlam]
                          · linarith only [h349, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          rcases p345_3 (m.d 0 2) (by simp) with h356 | h356
                          · rcases p345_3 (m.d 1 2) (by simp) with h357 | h357
                            · rcases p345_3 (m.d 2 3) (by simp) with h358 | h358
                              · linarith only [h331, h358, hlam]
                              · linarith only [h338, h358, hlam]
                            · linarith only [h336, h357, hlam]
                          · linarith only [h356, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [hc02, hlam, hphi, p345_1, u2elo1]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h338, h343, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p345_1, u2elo1]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          rcases p345_3 (m.d 0 2) (by simp) with h366 | h366
                          · linarith only [h0, h366, hlam]
                          · linarith only [h332, h366, hlam]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          rcases p345_3 (m.d 0 2) (by simp) with h369 | h369
                          · linarith only [h0, h369, hlam]
                          · linarith only [h333, h369, hlam]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h331, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h334, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h331, h337, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p345_1, u2elo0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h0, h331, h338, h343, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p345_1, u2elo1]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h332, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h335, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h337, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h339, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h333, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h336, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h338, hlam, p345_0]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [h336, h337, hc34, hlam, hphi, ht45, p345_1, u5elo1]
                        · have p345_0 := h345c.1
                          have p345_1 := h345c.2.1
                          have p345_2 := h345c.2.2.1
                          have p345_3 := h345c.2.2.2
                          linarith only [hlam, p345_0]
                  · linarith only [h337, h338, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h388 | h388
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h389 | h389
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h390 | h390
                      · rcases h2bigk with h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c | h391c
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h0, hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h0, h388, h390, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p391_1, u2elo1]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h0, h337, h388, h390, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p391_1, u2elo1]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          rcases p391_3 (m.d 0 2) (by simp) with h396 | h396
                          · rcases p391_3 (m.d 1 2) (by simp) with h397 | h397
                            · rcases p391_3 (m.d 2 3) (by simp) with h398 | h398
                              · linarith only [h331, h398, hlam]
                              · linarith only [h388, h398, hlam]
                            · linarith only [h336, h397, hlam]
                          · linarith only [h396, hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [hc02, hlam, hphi, p391_1, u2elo1]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h388, h390, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p391_1, u2elo1]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h337, h388, h390, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p391_1, u2elo1]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          rcases p391_3 (m.d 0 2) (by simp) with h407 | h407
                          · linarith only [h0, h407, hlam]
                          · linarith only [h333, h407, hlam]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h331, hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h334, hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h337, hlam, p391_1]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h337, h388, h390, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p391_1, u3elo3]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h332, hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h335, hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h0, h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p391_1, u2elo1]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h0, h332, h388, h390, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p391_1, u2elo1]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h333, hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h336, hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h388, hlam, p391_0]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [h389, hlam, p391_1]
                        · have p391_0 := h391c.1
                          have p391_1 := h391c.2.1
                          have p391_2 := h391c.2.2.1
                          have p391_3 := h391c.2.2.2
                          linarith only [hlam, p391_0]
                      · linarith only [h337, h390, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h337, h388, h389, hc35, hlam, hphi, u5elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h427 | h427
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h428 | h428
                      · rcases h2bigk with h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h0, hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          rcases p429_3 (m.d 0 2) (by simp) with h432 | h432
                          · rcases p429_3 (m.d 1 2) (by simp) with h433 | h433
                            · rcases p429_3 (m.d 2 3) (by simp) with h434 | h434
                              · linarith only [h434, hlam, p429_0]
                              · rcases p429_3 (m.d 2 4) (by simp) with h436 | h436
                                · linarith only [h332, h436, hlam]
                                · linarith only [h337, h436, hlam]
                            · linarith only [h334, h433, hlam]
                          · linarith only [h432, hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h0, h427, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p429_1, u2elo1]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          rcases p429_3 (m.d 0 2) (by simp) with h442 | h442
                          · rcases p429_3 (m.d 1 2) (by simp) with h443 | h443
                            · rcases p429_3 (m.d 2 3) (by simp) with h444 | h444
                              · linarith only [h331, h444, hlam]
                              · rcases p429_3 (m.d 2 4) (by simp) with h446 | h446
                                · linarith only [h332, h446, hlam]
                                · linarith only [h427, h446, hlam]
                            · linarith only [h336, h443, hlam]
                          · linarith only [h442, hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [hc02, hlam, hphi, p429_1, u2elo1]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          rcases p429_3 (m.d 0 2) (by simp) with h453 | h453
                          · linarith only [h0, h453, hlam]
                          · linarith only [h331, h453, hlam]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h427, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p429_1, u2elo1]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          rcases p429_3 (m.d 0 2) (by simp) with h457 | h457
                          · linarith only [h0, h457, hlam]
                          · linarith only [h333, h457, hlam]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h331, hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h334, hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h337, hlam, p429_1]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h388, hlam, p429_1]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h332, hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h335, hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p429_1, u2elo0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h0, h332, h388, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p429_1, u2elo1]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h333, hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h336, hlam, p429_0]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [hc23, hlam, hphi, ht34, ht45, p429_1, u5elo2]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [h427, hlam, p429_1]
                        · have p429_0 := h429c.1
                          have p429_1 := h429c.2.1
                          have p429_2 := h429c.2.2.1
                          have p429_3 := h429c.2.2.2
                          linarith only [hlam, p429_0]
                      · linarith only [h337, h428, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h476 | h476
                      · linarith only [h337, h427, h476, hc23, hlam, hphi, u3elo3]
                      · linarith only [h337, h476, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h336, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h332, h335, hlam]
          · linarith only [h0, h334, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h331, h333, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h483 | h483
        · rcases m.htr 1 2 3 (by decide) (by decide) with h484 | h484
          · rcases m.htr 1 2 4 (by decide) (by decide) with h485 | h485
            · linarith only [h331, h332, h485, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
            · linarith only [h0, h485, hc01, hlam, hphi, ht12, u2elo3]
          · linarith only [h0, h484, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h331, h483, hc23, hlam, hphi, ht34, ht45, u5elo2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h490 | h490
      · rcases m.htr 0 2 5 (by decide) (by decide) with h491 | h491
        · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
          · linarith only [h331, h490, h492, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
          · linarith only [h0, h492, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h490, h491, hc24, hlam, hphi, ht45, u5elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h496 | h496
        · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
          · linarith only [h331, h497, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h497, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h500 | h500
          · linarith only [h331, h500, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h500, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
