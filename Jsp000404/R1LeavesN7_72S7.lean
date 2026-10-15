import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_I_L_0_L_0_L_0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3elo := hb3.1
  have h5elo := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h10, h12, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases h0bigk with h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c | h14c
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h0, h12, h5, h7, h8, hc01, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1, u3elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h5, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h0, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h5, h7, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14_1, u2elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p14_1, u2elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h1, hlam, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h3, hlam, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p14_1, u3elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p14_1, u3elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h2, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h4, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h5, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h7, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p14_1, u5elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h12, h5, h7, hc02, hc34, hlam, hphi, ht23, ht45, p14_1, u3elo0, u5elo0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h6, hlam, p14_0]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [h7, hlam, p14_1]
                          · have p14_0 := h14c.1
                            have p14_1 := h14c.2.1
                            have p14_2 := h14c.2.2.1
                            have p14_3 := h14c.2.2.2
                            linarith only [hlam, p14_0]
                      · linarith only [h10, h11, hc34, hlam, hphi, ht45, u5elo3]
                    · linarith only [h10, h5, hc23, hlam, hphi, u3elo0]
                  · linarith only [h4, h8, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                        · linarith only [h0, h44, h46, h48, h7, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h0, h44, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h3, h47, hc01, hc35, hlam, hphi, ht0b, ht5b, p50_1]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            rcases p50_3 (m.d 0 1) (by simp) with h54 | h54
                            · rcases p50_3 (m.d 0 2) (by simp) with h55 | h55
                              · linarith only [h0, h55, hlam]
                              · linarith only [h4, h55, hlam]
                            · linarith only [h2, h54, hlam]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            rcases p50_3 (m.d 0 1) (by simp) with h59 | h59
                            · rcases p50_3 (m.d 0 2) (by simp) with h60 | h60
                              · linarith only [h0, h60, hlam]
                              · linarith only [h0, h44, h47, h48, h60, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p50_1]
                            · linarith only [h59, hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h0, hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h1, h44, h47, h48, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p50_1, u2elo0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h2, h45, h46, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p50_1, u2elo0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p50_1, u2elo0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h1, hlam, p50_1]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h3, hlam, p50_1]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h2, h45, h46, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p50_1, u3elo0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p50_1, u3elo0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h2, hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h4, hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h5, hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h7, hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p50_1, u5elo0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h0, h44, h47, h48, h7, hc34, hlam, hphi, ht45, p50_1, u5elo4]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h6, hlam, p50_0]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [h2, h45, h46, h7, hc34, hlam, hphi, ht45, p50_1, u5elo4]
                          · have p50_0 := h50c.1
                            have p50_1 := h50c.2.1
                            have p50_2 := h50c.2.2.1
                            have p50_3 := h50c.2.2.2
                            linarith only [hlam, p50_0]
                      · linarith only [h47, h6, hc23, hlam, hphi, u3elo0]
                    · linarith only [h46, h5, hc23, hlam, hphi, u3elo0]
                  · linarith only [h4, h44, h45, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                · linarith only [h3, h44, hc12, hlam, hphi, u2elo0]
            · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h89 | h89
            · rcases m.htr 0 4 5 (by decide) (by decide) with h90 | h90
              · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
                · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h93 | h93
                    · linarith only [h5, h89, h91, h93, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h95 | h95
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                        · rcases h0bigk with h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [hlam, p97_0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h0, h92, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p97_1]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h1, h91, h95, h96, hc01, hc45, hlam, hphi, ht0b, ht5b, p97_1]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h1, h5, h91, h95, h96, hc01, hc45, hlam, hphi, ht0b, ht5b, p97_1]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            rcases p97_3 (m.d 0 1) (by simp) with h102 | h102
                            · rcases p97_3 (m.d 0 2) (by simp) with h103 | h103
                              · linarith only [h0, h103, hlam]
                              · linarith only [h0, h103, h92, h93, h95, h96, hc01, hc45, hlam, hphi, ht0b, ht5b, p97_1]
                            · linarith only [h102, hlam, p97_0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h0, hlam, p97_0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [hlam, p97_0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h1, h91, h95, h96, hc02, hc45, hlam, hphi, ht0b, ht5b, p97_1]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h1, h5, h91, h95, h96, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p97_1, u2elo0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p97_1, u2elo0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h1, hlam, p97_1]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h3, hlam, p97_1]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [hlam, p97_0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h5, hlam, p97_1]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h5, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p97_1, u3elo3]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h2, hlam, p97_0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h4, hlam, p97_0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h1, h91, h95, h96, hc04, hc45, hlam, hphi, ht0b, ht5b, p97_1]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [hlam, p97_0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h5, h89, h96, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p97_1, u3elo3]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p97_1, u5elo0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h89, hc02, hlam, hphi, ht23, p97_1, u3elo0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h89, hlam, p97_0]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [h90, hlam, p97_1]
                          · have p97_0 := h97c.1
                            have p97_1 := h97c.2.1
                            have p97_2 := h97c.2.2.1
                            have p97_3 := h97c.2.2.2
                            linarith only [hlam, p97_0]
                        · linarith only [h5, h96, hc03, hlam, hphi, ht34, ht45, u5elo4]
                      · linarith only [h5, h89, h95, hc23, hlam, hphi, u3elo3]
                  · linarith only [h4, h92, hc12, hlam, hphi, u2elo0]
                · linarith only [h3, h91, hc12, hlam, hphi, u2elo0]
              · linarith only [h5, h89, h90, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h132 | h132
              · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
                · rcases m.htr 1 2 4 (by decide) (by decide) with h134 | h134
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                    · linarith only [h1, h133, h135, h5, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h137 | h137
                      · linarith only [h1, h133, h137, h89, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
                        · rcases h0bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h0, h134, h135, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            rcases p140_3 (m.d 0 1) (by simp) with h143 | h143
                            · rcases p140_3 (m.d 0 2) (by simp) with h144 | h144
                              · linarith only [h0, h144, hlam]
                              · linarith only [h144, h3, hlam]
                            · linarith only [h1, h143, hlam]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h132, hc01, hc45, hlam, hphi, ht0b, ht5b, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            rcases p140_3 (m.d 0 1) (by simp) with h149 | h149
                            · rcases p140_3 (m.d 0 2) (by simp) with h150 | h150
                              · linarith only [h0, h150, hlam]
                              · linarith only [h0, h134, h135, h150, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p140_1]
                            · linarith only [h149, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h0, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p140_1, u2elo0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h132, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p140_1, u2elo0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p140_1, u2elo0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h1, hlam, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h3, hlam, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h5, hlam, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h89, hlam, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h2, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h4, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h1, h133, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p140_1, u2elo0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h1, h133, h5, h89, hc23, hlam, hphi, p140_1, u3elo3]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p140_1, u5elo0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h89, hc02, hlam, hphi, ht23, p140_1, u3elo4]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h1, h133, h89, hc23, hlam, hphi, ht34, ht45, p140_1, u5elo3]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h132, hlam, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hlam, p140_0]
                        · linarith only [h1, h133, h139, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h134, h4, hc12, hlam, hphi, u2elo0]
                · linarith only [h133, h3, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
                · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
                    · linarith only [h1, h177, h179, h5, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h181 | h181
                      · linarith only [h132, h179, h181, h4, hc35, hlam, hphi, u5elo4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h183 | h183
                        · linarith only [h132, h183, h5, hc03, hlam, hphi, u3elo3]
                        · linarith only [h1, h177, h183, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
                  · linarith only [h178, h4, hc12, hlam, hphi, u2elo0]
                · linarith only [h177, h3, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h188 | h188
          · linarith only [h188, h3, h4, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
            · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
              · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
                  · linarith only [h0, h193, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                    · linarith only [h0, h188, h192, h195, h4, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h0, h192, h195, h4, hc23, hlam, hphi, u3elo3]
                · linarith only [h192, h3, h4, hc12, hlam, hphi, u2elo3]
              · linarith only [h191, h3, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h200 | h200
              · rcases m.htr 1 2 3 (by decide) (by decide) with h201 | h201
                · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                  · linarith only [h0, h202, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                    · linarith only [h0, h201, h204, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                    · linarith only [h0, h201, h204, h4, hc23, hlam, hphi, u3elo3]
                · linarith only [h201, h3, h4, hc12, hlam, hphi, u2elo3]
              · linarith only [h200, h3, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h209 | h209
        · rcases m.htr 0 3 4 (by decide) (by decide) with h210 | h210
          · rcases m.htr 0 3 5 (by decide) (by decide) with h211 | h211
            · rcases m.htr 0 4 5 (by decide) (by decide) with h212 | h212
              · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                · linarith only [h209, h213, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h216 | h216
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h217 | h217
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h218 | h218
                        · linarith only [h0, h215, h216, h218, h3, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                        · linarith only [h209, h212, h218, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                      · linarith only [h0, h211, h215, h217, h3, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h215, h216, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h209, h215, h3, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
                · linarith only [h224, h3, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h226 | h226
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h228 | h228
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h229 | h229
                        · linarith only [h0, h212, h226, h227, h229, h3, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                        · rcases h0bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h209, h227, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h209, h227, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            rcases p231_3 (m.d 0 1) (by simp) with h235 | h235
                            · rcases p231_3 (m.d 0 2) (by simp) with h236 | h236
                              · linarith only [h0, h236, hlam]
                              · linarith only [h209, h236, hlam]
                            · linarith only [h2, h235, hlam]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            rcases p231_3 (m.d 0 1) (by simp) with h240 | h240
                            · rcases p231_3 (m.d 0 2) (by simp) with h241 | h241
                              · linarith only [h0, h241, hlam]
                              · linarith only [h0, h226, h227, h241, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p231_1]
                            · linarith only [h240, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h3, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h2, h226, h227, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p231_1, u2elo0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p231_1, u2elo0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h1, hlam, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, p231_1, u3elo0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h2, h226, h227, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p231_1, u3elo2]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h3, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p231_1, u3elo2]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h2, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h209, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h210, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h212, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h212, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, h212, h226, h227, hc34, hlam, hphi, ht45, p231_1, u5elo4]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h211, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h212, hc04, hlam, hphi, ht45, p231_1, u5elo4]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                      · linarith only [h211, h228, h3, hlam]
                    · linarith only [h0, h226, h227, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                  · linarith only [h209, h226, h3, hc12, hlam, hphi, u2elo2]
            · linarith only [h209, h211, h3, hc24, hlam, hphi, ht45, u5elo3]
          · linarith only [h209, h210, h3, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h270 | h270
          · rcases m.htr 0 3 5 (by decide) (by decide) with h271 | h271
            · rcases m.htr 0 4 5 (by decide) (by decide) with h272 | h272
              · rcases m.htr 1 2 3 (by decide) (by decide) with h273 | h273
                · linarith only [h273, h3, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h275 | h275
                  · linarith only [h0, h209, h275, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h277 | h277
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h279 | h279
                        · rcases h0bigk with h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c | h280c
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            rcases p280_3 (m.d 0 1) (by simp) with h282 | h282
                            · rcases p280_3 (m.d 0 2) (by simp) with h283 | h283
                              · linarith only [h0, h283, hlam]
                              · rcases p280_3 (m.d 0 3) (by simp) with h285 | h285
                                · linarith only [h1, h285, hlam]
                                · linarith only [h285, h3, hlam]
                            · linarith only [h0, h282, hlam]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h270, h279, hc01, hc45, hlam, hphi, ht0b, ht5b, p280_1]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h270, h279, hc01, hc45, hlam, hphi, ht0b, ht5b, p280_1]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            rcases p280_3 (m.d 0 1) (by simp) with h291 | h291
                            · rcases p280_3 (m.d 0 2) (by simp) with h292 | h292
                              · linarith only [h0, h292, hlam]
                              · rcases p280_3 (m.d 0 3) (by simp) with h294 | h294
                                · linarith only [h1, h294, hlam]
                                · linarith only [h271, h294, hlam]
                            · linarith only [h291, hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h0, hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h3, hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h209, hlam, p280_1]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h209, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p280_1, u2elo3]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h1, hlam, p280_1]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [hc02, hlam, hphi, ht23, p280_1, u3elo0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h2, h275, h3, hc12, hlam, hphi, ht23, p280_1, u3elo2]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h271, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p280_1, u3elo2]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h2, hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h0, h209, hc12, hlam, hphi, p280_1, u2elo3]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h270, hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h270, h271, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p280_1, u3elo2]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h1, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p280_1]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h0, h270, h272, hc12, hlam, hphi, ht23, p280_1, u3elo0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h271, hlam, p280_0]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [h272, hlam, p280_1]
                          · have p280_0 := h280c.1
                            have p280_1 := h280c.2.1
                            have p280_2 := h280c.2.2.1
                            have p280_3 := h280c.2.2.2
                            linarith only [hlam, p280_0]
                        · rcases h0bigk with h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [hlam, p318_0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            rcases p318_3 (m.d 0 1) (by simp) with h320 | h320
                            · rcases p318_3 (m.d 0 2) (by simp) with h321 | h321
                              · linarith only [h0, h321, hlam]
                              · rcases p318_3 (m.d 0 3) (by simp) with h323 | h323
                                · linarith only [h1, h323, hlam]
                                · linarith only [h3, h323, hlam]
                            · linarith only [h0, h320, hlam]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h270, h272, h279, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p318_1]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h272, h279, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p318_1]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h272, h279, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p318_1]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h0, hlam, p318_0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [hlam, p318_0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h3, hlam, p318_0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h209, hlam, p318_1]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h272, h279, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p318_1]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h1, hlam, p318_1]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h3, hc02, hlam, hphi, ht23, p318_1, u3elo2]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [hlam, p318_0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h272, h279, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p318_1, u3elo2]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h272, h279, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p318_1, u3elo2]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h2, hlam, p318_0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h0, h209, h277, hc12, hlam, hphi, ht23, p318_1, u3elo2]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h270, hlam, p318_0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [hlam, p318_0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h209, h272, h277, h279, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p318_1, u3elo2]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p318_1, u5elo0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h0, h209, h272, h277, h279, hc12, hc34, hlam, hphi, ht23, ht45, p318_1, u3elo2, u5elo0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h271, hlam, p318_0]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [h272, hlam, p318_1]
                          · have p318_0 := h318c.1
                            have p318_1 := h318c.2.1
                            have p318_2 := h318c.2.2.1
                            have p318_3 := h318c.2.2.2
                            linarith only [hlam, p318_0]
                      · linarith only [h209, h272, h277, h278, hc45, hlam, hphi, u5elo3]
                    · linarith only [h0, h277, h3, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
                · linarith only [h0, h3, h352, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
                  · linarith only [h0, h209, h354, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h356 | h356
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h357 | h357
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h358 | h358
                        · linarith only [h0, h209, h272, h358, hc12, hlam, hphi, ht23, u3elo3]
                        · rcases h0bigk with h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c | h360c
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            rcases p360_3 (m.d 0 1) (by simp) with h362 | h362
                            · rcases p360_3 (m.d 0 2) (by simp) with h363 | h363
                              · linarith only [h0, h363, hlam]
                              · rcases p360_3 (m.d 0 3) (by simp) with h365 | h365
                                · linarith only [h1, h365, hlam]
                                · linarith only [h3, h365, hlam]
                            · linarith only [h0, h362, hlam]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h271, hc01, hc35, hlam, hphi, ht0b, ht5b, p360_1]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            rcases p360_3 (m.d 0 1) (by simp) with h370 | h370
                            · rcases p360_3 (m.d 0 2) (by simp) with h371 | h371
                              · linarith only [h0, h371, hlam]
                              · rcases p360_3 (m.d 0 3) (by simp) with h373 | h373
                                · linarith only [h1, h373, hlam]
                                · linarith only [h270, h373, hlam]
                            · linarith only [h2, h370, hlam]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            rcases p360_3 (m.d 0 1) (by simp) with h377 | h377
                            · rcases p360_3 (m.d 0 2) (by simp) with h378 | h378
                              · linarith only [h0, h378, hlam]
                              · rcases p360_3 (m.d 0 3) (by simp) with h380 | h380
                                · linarith only [h1, h380, hlam]
                                · linarith only [h271, h380, hlam]
                            · linarith only [h377, hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h0, hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h3, hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h209, hlam, p360_1]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h209, h272, hlam, p360_1]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h1, hlam, p360_1]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht23, p360_1, u3elo0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h0, h209, h3, hc12, hlam, hphi, ht23, p360_1, u3elo2]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h0, h209, h272, h3, hc12, hlam, hphi, ht23, p360_1, u3elo2]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h2, hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h0, h272, hc12, hc45, hlam, hphi, ht23, ht34, p360_1]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h270, hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h272, hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h272, hc01, hlam, hphi, ht12, ht23, ht34, ht45, p360_1, u5elo4]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h0, h271, hc12, hlam, hphi, ht23, p360_1, u3elo0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h271, hlam, p360_0]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [h272, hc04, hlam, hphi, ht45, p360_1, u5elo4]
                          · have p360_0 := h360c.1
                            have p360_1 := h360c.2.1
                            have p360_2 := h360c.2.2.1
                            have p360_3 := h360c.2.2.2
                            linarith only [hlam, p360_0]
                      · linarith only [h0, h3, h357, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h3, h356, hc12, hlam, hphi, ht23, u3elo3]
            · linarith only [h270, h271, hc34, hlam, hphi, ht45, u5elo3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h407 | h407
            · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
              · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
                · linarith only [h0, h3, h409, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h411 | h411
                  · linarith only [h0, h209, h411, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h413 | h413
                    · linarith only [h270, h407, h413, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                    · linarith only [h3, h413, hc02, hlam, hphi, ht23, u3elo3]
              · linarith only [h270, h407, h408, hc35, hlam, hphi, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h417 | h417
              · rcases m.htr 1 2 3 (by decide) (by decide) with h418 | h418
                · linarith only [h0, h3, h418, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h420 | h420
                  · linarith only [h0, h3, h407, h420, hc24, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h422 | h422
                    · linarith only [h0, h270, h3, h422, hc12, hlam, hphi, u2elo2]
                    · linarith only [h0, h3, h422, hc12, hlam, hphi, ht23, u3elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
                · linarith only [h0, h3, h425, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h427 | h427
                  · linarith only [h0, h209, h427, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h429 | h429
                    · linarith only [h0, h270, h3, h429, hc12, hlam, hphi, u2elo2]
                    · linarith only [h0, h3, h429, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h432 | h432
      · rcases m.htr 0 2 4 (by decide) (by decide) with h433 | h433
        · linarith only [h0, h2, h433, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h435 | h435
          · linarith only [h1, h2, h435, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h437 | h437
            · rcases m.htr 0 4 5 (by decide) (by decide) with h438 | h438
              · rcases m.htr 1 2 3 (by decide) (by decide) with h439 | h439
                · linarith only [h0, h2, h435, h439, hc23, hlam, hphi, u3elo3]
                · linarith only [h432, h439, hc12, hlam, hphi, u2elo0]
              · linarith only [h0, h2, h438, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h443 | h443
              · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
                · linarith only [h0, h2, h435, h444, hc23, hlam, hphi, u3elo3]
                · linarith only [h432, h433, h444, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h2, h443, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h448 | h448
        · linarith only [h0, h2, h432, h448, hc12, hlam, hphi, ht23, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h450 | h450
          · linarith only [h1, h2, h450, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h452 | h452
            · rcases m.htr 0 4 5 (by decide) (by decide) with h453 | h453
              · rcases m.htr 1 2 3 (by decide) (by decide) with h454 | h454
                · linarith only [h0, h432, h450, h454, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
                  · linarith only [h1, h2, h448, h454, h456, hlam]
                  · linarith only [h1, h2, h454, h456, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h2, h453, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h460 | h460
              · rcases m.htr 1 2 3 (by decide) (by decide) with h461 | h461
                · linarith only [h432, h461, hc02, hlam, hphi, u2elo1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h463 | h463
                  · linarith only [h0, h432, h452, h463, hc24, hlam, hphi, ht45, u5elo3]
                  · linarith only [h1, h2, h461, h463, hc12, hlam, hphi, u2elo3]
              · linarith only [h0, h2, h460, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
  · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

end R2N4
