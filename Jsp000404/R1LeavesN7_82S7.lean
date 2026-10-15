import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_L_L_0_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h2, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h2, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h11 | h11
          · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
            · linarith only [h0, h12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h12, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
            · linarith only [h0, h15, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · linarith only [h0, h15, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h18 | h18
        · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
          · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
            · linarith only [h0, h2, h20, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h22 | h22
              · linarith only [h1, h22, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h1, h18, h22, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
            · linarith only [h0, h18, h2, h25, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
              · linarith only [h1, h27, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h18, h25, h27, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
          · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
            · linarith only [h0, h2, h31, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h33 | h33
              · linarith only [h18, h30, h33, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h35 | h35
                · linarith only [h1, h35, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h30, h35, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
            · linarith only [h0, h2, h38, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
              · linarith only [h1, h18, h40, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                · linarith only [h1, h30, h42, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                        · rcases h3bigk with h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c | h48c
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p48_1, u0elo2]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h2, hlam, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h18, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h30, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h1, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h38, hlam, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h40, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h42, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            rcases p48_3 (m.d 0 3) (by simp) with h59 | h59
                            · linarith only [h2, h59, hlam]
                            · rcases p48_3 (m.d 1 3) (by simp) with h61 | h61
                              · linarith only [h38, h61, hlam]
                              · rcases p48_3 (m.d 2 3) (by simp) with h63 | h63
                                · rcases p48_3 (m.d 3 4) (by simp) with h64 | h64
                                  · linarith only [h44, h64, hlam]
                                  · linarith only [h18, h64, hlam]
                                · linarith only [h2, h63, hlam]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            rcases p48_3 (m.d 0 3) (by simp) with h68 | h68
                            · linarith only [h2, h68, hlam]
                            · linarith only [h1, h68, hlam]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h1, h30, h38, h47, hc12, hc23, hlam, hphi, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h1, h30, h38, hc12, hc23, hlam, hphi, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h1, h38, h44, hc12, hlam, hphi, ht23, ht34, p48_1, u4elo2]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h38, h44, hc12, hlam, hphi, ht23, ht34, p48_1, u4elo2]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h44, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h1, h30, h38, h44, hc12, hlam, hphi, ht23, ht34, p48_1, u4elo2]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h1, h38, h45, hc12, hc23, hlam, hphi, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h38, h45, hc12, hc23, hlam, hphi, p48_1]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h45, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [h47, hlam, p48_0]
                          · have p48_0 := h48c.1
                            have p48_1 := h48c.2.1
                            have p48_2 := h48c.2.2.1
                            have p48_3 := h48c.2.2.2
                            linarith only [hlam, p48_0]
                        · linarith only [h1, h18, h38, h47, hc12, hlam, hphi, ht23, ht34, u4elo4]
                      · linarith only [h1, h18, h38, h44, h46, hc12, hlam, hphi, ht23, ht34, u4elo4]
                    · linarith only [h1, h18, h38, h44, h45, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h2, h44, hc12, hlam, hphi, ht23, ht34, u4elo3]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h88 | h88
      · linarith only [h0, h1, h88, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
        · rcases m.htr 0 3 5 (by decide) (by decide) with h91 | h91
          · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
            · linarith only [h0, h88, h92, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
              · rcases m.htr 1 3 5 (by decide) (by decide) with h95 | h95
                · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                        · linarith only [h90, h99, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h98, h99, hc34, hlam, hphi, u4elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                        · linarith only [h102, h98, hc24, hlam, hphi, u4elo3]
                        · rcases h3bigk with h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c | h104c
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h1, hlam, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h88, hlam, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p104_1, u0elo2]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hc35, hlam, hphi, ht0b, ht5b, p104_1, u0elo2]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, p104_1, u1elo2]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h92, hlam, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            rcases p104_3 (m.d 0 3) (by simp) with h113 | h113
                            · linarith only [h1, h113, hlam]
                            · linarith only [h113, h90, hlam]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            rcases p104_3 (m.d 0 3) (by simp) with h116 | h116
                            · linarith only [h1, h116, hlam]
                            · linarith only [h116, h91, hlam]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h0, h1, hc12, hc23, hlam, hphi, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h0, h1, hc12, hc23, hlam, hphi, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            rcases p104_3 (m.d 0 3) (by simp) with h122 | h122
                            · linarith only [h122, h88, hlam]
                            · linarith only [h122, h90, hlam]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            rcases p104_3 (m.d 0 3) (by simp) with h125 | h125
                            · linarith only [h125, h88, hlam]
                            · linarith only [h125, h91, hlam]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h90, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h94, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h96, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h102, hlam, p104_1]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h91, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h95, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h97, hlam, p104_0]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [h91, hc34, hlam, hphi, ht0b, ht45, ht5b, p104_1, u0elo2]
                          · have p104_0 := h104c.1
                            have p104_1 := h104c.2.1
                            have p104_2 := h104c.2.2.1
                            have p104_3 := h104c.2.2.2
                            linarith only [hlam, p104_0]
                    · linarith only [h91, h97, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h1, h92, h96, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h91, h95, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h0, h1, h90, h94, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
            · linarith only [h0, h142, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
              · rcases m.htr 1 3 5 (by decide) (by decide) with h145 | h145
                · linarith only [h1, h145, h91, hc01, hlam, hphi, u1elo2]
                · linarith only [h0, h1, h145, hc12, hc35, hlam, hphi, ht23]
              · linarith only [h0, h1, h144, h90, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
        · linarith only [h0, h1, h90, hc12, hlam, hphi, ht23, ht34, u4elo3]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h150 | h150
    · rcases m.htr 0 2 3 (by decide) (by decide) with h151 | h151
      · rcases m.htr 0 3 4 (by decide) (by decide) with h152 | h152
        · rcases m.htr 0 3 5 (by decide) (by decide) with h153 | h153
          · rcases m.htr 1 2 3 (by decide) (by decide) with h154 | h154
            · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
              · linarith only [h150, h155, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h152, h155, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h151, h154, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
            · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
              · linarith only [h150, h160, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h152, h160, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h151, h159, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
          · rcases m.htr 1 2 3 (by decide) (by decide) with h165 | h165
            · rcases m.htr 1 3 4 (by decide) (by decide) with h166 | h166
              · linarith only [h150, h152, h166, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h168 | h168
                · linarith only [h0, h150, h168, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                · linarith only [h164, h168, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h151, h165, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h172 | h172
            · rcases m.htr 1 3 4 (by decide) (by decide) with h173 | h173
              · linarith only [h150, h152, h173, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h175 | h175
                · linarith only [h150, h164, h175, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h177 | h177
                  · linarith only [h150, h152, h172, h177, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h179 | h179
                    · linarith only [h150, h164, h172, h179, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h181 | h181
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h182 | h182
                        · rcases h3bigk with h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c | h183c
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h172, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p183_1, u0elo2]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h164, h182, hc23, hlam, hphi, ht34, p183_1, u4elo3]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h152, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h164, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h150, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h0, h150, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p183_1, u1elo1]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h173, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h175, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h151, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h172, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h177, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h179, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [hc03, hlam, hphi, ht34, p183_1, u4elo3]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [hc13, hlam, hphi, ht34, p183_1, u4elo3]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [hc23, hlam, hphi, ht34, p183_1, u4elo3]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h150, h164, h172, hc23, hlam, hphi, ht34, p183_1, u4elo3]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h150, h172, h182, hc23, hlam, hphi, ht34, p183_1, u4elo3]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h172, h182, hc23, hlam, hphi, ht34, p183_1, u4elo3]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h182, hc23, hlam, hphi, ht34, p183_1, u4elo3]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [h182, hlam, p183_0]
                          · have p183_0 := h183c.1
                            have p183_1 := h183c.2.1
                            have p183_2 := h183c.2.2.1
                            have p183_3 := h183c.2.2.2
                            linarith only [hlam, p183_0]
                        · linarith only [h181, h182, hc34, hlam, hphi, u4elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                        · linarith only [h181, h210, hc24, hlam, hphi, u4elo3]
                        · linarith only [h150, h152, h172, h210, hc23, hlam, hphi, ht34, u4elo4]
            · linarith only [h0, h151, h172, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h150, h151, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h215 | h215
      · rcases m.htr 0 3 4 (by decide) (by decide) with h216 | h216
        · rcases m.htr 0 3 5 (by decide) (by decide) with h217 | h217
          · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
            · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
              · rcases m.htr 1 3 5 (by decide) (by decide) with h220 | h220
                · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                  · linarith only [h215, h221, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h215, h216, h221, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                · linarith only [h150, h215, h217, h220, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h150, h216, h219, hlam]
            · linarith only [h215, h218, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
            · rcases m.htr 1 3 4 (by decide) (by decide) with h228 | h228
              · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                · linarith only [h216, h217, h229, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h231 | h231
                  · linarith only [h215, h231, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h216, h231, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h216, h217, h228, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
            · linarith only [h215, h227, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h236 | h236
          · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
            · rcases m.htr 1 3 4 (by decide) (by decide) with h238 | h238
              · linarith only [h216, h236, h238, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · linarith only [h150, h238, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h215, h237, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
            · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
              · linarith only [h150, h216, h243, hc01, hlam, hphi, u1elo2]
              · linarith only [h150, h243, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h0, h215, h242, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h247 | h247
        · rcases m.htr 0 3 5 (by decide) (by decide) with h248 | h248
          · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
            · linarith only [h0, h215, h249, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h251 | h251
              · rcases m.htr 1 3 5 (by decide) (by decide) with h252 | h252
                · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h254 | h254
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h255 | h255
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h256 | h256
                        · linarith only [h247, h256, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                        · linarith only [h255, h256, hc34, hlam, hphi, u4elo2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                        · linarith only [h255, h259, hc24, hlam, hphi, u4elo3]
                        · rcases h3bigk with h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c | h261c
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h150, hlam, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h215, hlam, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p261_1, u0elo2]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hc35, hlam, hphi, ht0b, ht5b, p261_1, u0elo2]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h150, hc01, hlam, hphi, p261_1, u1elo2]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h249, hlam, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            rcases p261_3 (m.d 0 3) (by simp) with h270 | h270
                            · linarith only [h150, h270, hlam]
                            · linarith only [h247, h270, hlam]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            rcases p261_3 (m.d 0 3) (by simp) with h273 | h273
                            · linarith only [h150, h273, hlam]
                            · linarith only [h248, h273, hlam]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            rcases p261_3 (m.d 0 3) (by simp) with h276 | h276
                            · linarith only [h215, h276, hlam]
                            · rcases p261_3 (m.d 1 3) (by simp) with h278 | h278
                              · linarith only [h249, h278, hlam]
                              · linarith only [h150, h278, hlam]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h150, hc01, hc23, hlam, hphi, ht12, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            rcases p261_3 (m.d 0 3) (by simp) with h283 | h283
                            · linarith only [h215, h283, hlam]
                            · linarith only [h247, h283, hlam]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            rcases p261_3 (m.d 0 3) (by simp) with h286 | h286
                            · linarith only [h215, h286, hlam]
                            · linarith only [h248, h286, hlam]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h247, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h251, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h253, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h259, hlam, p261_1]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h248, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h252, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h254, hlam, p261_0]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [h248, hc34, hlam, hphi, ht0b, ht45, ht5b, p261_1, u0elo2]
                          · have p261_0 := h261c.1
                            have p261_1 := h261c.2.1
                            have p261_2 := h261c.2.2.1
                            have p261_3 := h261c.2.2.2
                            linarith only [hlam, p261_0]
                    · linarith only [h248, h254, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h0, h249, h253, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h0, h248, h249, h252, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h150, h247, h251, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
            · linarith only [h0, h215, h303, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h305 | h305
              · rcases m.htr 1 3 5 (by decide) (by decide) with h306 | h306
                · linarith only [h247, h248, h306, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h309 | h309
                    · linarith only [h0, h303, h306, h309, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h303, h309, hc01, hc35, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h247, h303, h308, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h150, h247, h305, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h314 | h314
          · rcases m.htr 1 2 3 (by decide) (by decide) with h315 | h315
            · linarith only [h0, h215, h315, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h317 | h317
              · linarith only [h247, h314, h317, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
              · linarith only [h150, h317, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
            · linarith only [h0, h215, h320, hc01, hlam, hphi, u1elo1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h322 | h322
              · linarith only [h150, h247, h322, hc01, hlam, hphi, u1elo2]
              · linarith only [h150, h322, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]

theorem r1l7_20_11_13_14_M_LI_L_I_L_0_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3elo := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h2, h5, h6, h9, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h4, h9, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                  · linarith only [h1, h12, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h12, h4, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h15 | h15
              · linarith only [h0, h15, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h17 | h17
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                  · linarith only [h1, h18, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h18, h4, hc13, hlam, hphi, u3elo0]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                  · linarith only [h1, h21, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h21, h4, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
            · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
              · linarith only [h0, h25, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                  · linarith only [h28, h4, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h31 | h31
                      · linarith only [h2, h31, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h1, h24, h25, h30, h31, h4, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                      · linarith only [h2, h34, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h25, h27, h34, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                  · linarith only [h1, h37, h4, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                    · linarith only [h1, h24, h27, h39, h4, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                      · linarith only [h2, h41, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                        · linarith only [h24, h25, h4, h43, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h24, h25, h43, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
              · linarith only [h0, h46, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                · rcases m.htr 1 3 4 (by decide) (by decide) with h49 | h49
                  · linarith only [h1, h4, h49, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                      · linarith only [h2, h52, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h46, h48, h52, hlam]
                    · linarith only [h24, h48, h51, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h1, h4, h56, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                      · linarith only [h2, h59, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h56, h58, h59, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                      · linarith only [h2, h62, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                        · linarith only [h4, h64, hc03, hlam, hphi, u3elo2]
                        · linarith only [h24, h64, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h67 | h67
          · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
            · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
              · linarith only [h0, h3, h69, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h71 | h71
                · linarith only [h0, h3, h71, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
                  · linarith only [h2, h68, h69, h73, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h67, h73, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h76 | h76
              · linarith only [h0, h76, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                · linarith only [h2, h3, h76, h78, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                  · linarith only [h1, h3, h78, h80, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · linarith only [h67, h80, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h83 | h83
            · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
              · linarith only [h0, h84, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                · linarith only [h2, h3, h84, h86, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                  · linarith only [h67, h88, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                    · linarith only [h1, h2, h3, h83, h84, h90, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2, h3, h83, h84, h90, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h93 | h93
              · linarith only [h1, h67, h83, h93, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h95 | h95
                · linarith only [h1, h3, h83, h95, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h97 | h97
                  · linarith only [h1, h67, h97, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                    · linarith only [h1, h3, h67, h99, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h2, h3, h99, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h102 | h102
        · rcases m.htr 0 3 4 (by decide) (by decide) with h103 | h103
          · linarith only [h1, h103, h2, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h105 | h105
            · linarith only [h0, h103, h105, h2, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h107 | h107
              · linarith only [h1, h103, h105, h107, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h109 | h109
                · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                  · linarith only [h1, h103, h110, h2, hlam]
                  · linarith only [h1, h105, h110, h2, hc12, hlam, hphi, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                  · linarith only [h1, h103, h113, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h113, h2, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h116 | h116
          · linarith only [h1, h116, h2, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h118 | h118
            · linarith only [h0, h116, h118, h2, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
              · linarith only [h1, h116, h118, h120, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h122 | h122
                · linarith only [h1, h102, h118, h122, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h124 | h124
                  · linarith only [h1, h116, h124, h2, hlam]
                  · linarith only [h1, h118, h124, h2, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h128 | h128
    · rcases m.htr 0 1 4 (by decide) (by decide) with h129 | h129
      · rcases m.htr 0 1 5 (by decide) (by decide) with h130 | h130
        · rcases m.htr 0 3 4 (by decide) (by decide) with h131 | h131
          · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
            · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
              · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                  · linarith only [h128, h135, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h131, h132, h135, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h128, h131, h134, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h128, h131, h133, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h0, h128, h131, h132, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
            · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
              · rcases m.htr 1 2 5 (by decide) (by decide) with h143 | h143
                · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                  · linarith only [h128, h131, h144, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h147 | h147
                      · linarith only [h0, h129, h147, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h144, h146, h147, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h150 | h150
                      · linarith only [h0, h129, h150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                        · linarith only [h128, h131, h141, h152, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                          · linarith only [h142, h150, h154, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                            · linarith only [h144, h150, h156, hc13, hlam, hphi, u3elo3]
                            · rcases h1bigk with h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c | h158c
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [hlam, p158_0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h0, hlam, p158_0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                rcases p158_3 (m.d 0 1) (by simp) with h161 | h161
                                · rcases p158_3 (m.d 1 2) (by simp) with h162 | h162
                                  · rcases p158_3 (m.d 1 3) (by simp) with h163 | h163
                                    · linarith only [h163, hlam, p158_0]
                                    · rcases p158_3 (m.d 1 4) (by simp) with h165 | h165
                                      · linarith only [h129, h165, hlam]
                                      · linarith only [h144, h165, hlam]
                                  · linarith only [h141, h162, hlam]
                                · linarith only [h161, hlam, p158_0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h0, h142, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p158_1, u4ehi2]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h0, h142, h150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p158_1, u4ehi2]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h129, h142, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p158_1, u4ehi2]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [hlam, p158_0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                rcases p158_3 (m.d 0 1) (by simp) with h174 | h174
                                · linarith only [h0, h174, hlam]
                                · linarith only [h128, h174, hlam]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                rcases p158_3 (m.d 0 1) (by simp) with h177 | h177
                                · linarith only [h0, h177, hlam]
                                · linarith only [h129, h177, hlam]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                rcases p158_3 (m.d 0 1) (by simp) with h180 | h180
                                · linarith only [h0, h180, hlam]
                                · linarith only [h130, h180, hlam]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h128, hlam, p158_0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h141, hlam, p158_1]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [hlam, p158_0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h144, hlam, p158_1]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h146, hlam, p158_1]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h129, hlam, p158_0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h142, hlam, p158_1]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h130, h150, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p158_1, u0elo0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [hlam, p158_0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h150, hlam, p158_1]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h130, hlam, p158_0]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h143, hlam, p158_1]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h0, h130, h141, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p158_1]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [h0, h130, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p158_1, u4ehi1]
                              · have p158_0 := h158c.1
                                have p158_1 := h158c.2.1
                                have p158_2 := h158c.2.2.1
                                have p158_3 := h158c.2.2.2
                                linarith only [hlam, p158_0]
                · linarith only [h0, h129, h142, h143, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h0, h129, h142, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h129, h141, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h201 | h201
          · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
            · rcases m.htr 1 2 4 (by decide) (by decide) with h203 | h203
              · rcases m.htr 1 2 5 (by decide) (by decide) with h204 | h204
                · rcases m.htr 1 3 4 (by decide) (by decide) with h205 | h205
                  · linarith only [h128, h205, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h201, h205, hc13, hlam, hphi, u3elo0]
                · linarith only [h0, h129, h203, h204, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h0, h129, h203, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h128, h201, h202, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
            · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
              · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
                · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                  · linarith only [h128, h201, h214, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
                    · linarith only [h128, h130, h201, h216, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h129, h130, h214, h216, hc13, hlam, hphi, u3elo4]
                · linarith only [h0, h129, h212, h213, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h0, h129, h212, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h129, h211, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h222 | h222
        · rcases m.htr 0 3 4 (by decide) (by decide) with h223 | h223
          · linarith only [h128, h129, h223, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h225 | h225
            · rcases m.htr 1 2 4 (by decide) (by decide) with h226 | h226
              · rcases m.htr 1 2 5 (by decide) (by decide) with h227 | h227
                · rcases m.htr 1 3 4 (by decide) (by decide) with h228 | h228
                  · linarith only [h223, h228, hc03, hlam, hphi, u3elo1]
                  · linarith only [h128, h129, h228, hc13, hlam, hphi, u3elo3]
                · linarith only [h129, h222, h226, h227, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 1 3 4 (by decide) (by decide) with h233 | h233
                  · linarith only [h128, h233, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h128, h129, h225, h233, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h222, h232, hlam]
            · linarith only [h0, h225, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h238 | h238
          · linarith only [h128, h129, h238, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
            · rcases m.htr 1 2 4 (by decide) (by decide) with h241 | h241
              · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
                · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                  · linarith only [h238, h243, hc03, hlam, hphi, u3elo1]
                  · linarith only [h128, h129, h240, h243, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h246 | h246
                  · linarith only [h128, h246, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h128, h129, h240, h246, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h249 | h249
                · rcases m.htr 1 3 4 (by decide) (by decide) with h250 | h250
                  · linarith only [h128, h250, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h128, h129, h240, h250, hc23, hlam, hphi, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
                  · linarith only [h128, h253, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h0, h128, h240, h241, h253, hc23, hlam, hphi, u3elo3]
            · linarith only [h0, h240, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h257 | h257
      · linarith only [h128, h257, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h259 | h259
        · rcases m.htr 0 3 4 (by decide) (by decide) with h260 | h260
          · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
            · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
              · rcases m.htr 1 2 5 (by decide) (by decide) with h263 | h263
                · rcases m.htr 1 3 4 (by decide) (by decide) with h264 | h264
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                      · linarith only [h257, h259, h264, h266, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
                      · linarith only [h257, h259, h266, hlam]
                    · linarith only [h128, h260, h265, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                  · linarith only [h128, h260, h264, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h259, h262, h263, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h272 | h272
                · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                  · linarith only [h261, h262, h273, hlam]
                  · linarith only [h128, h260, h273, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h128, h259, h261, h272, hlam]
            · linarith only [h0, h261, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h278 | h278
            · rcases m.htr 1 2 4 (by decide) (by decide) with h279 | h279
              · rcases m.htr 1 2 5 (by decide) (by decide) with h280 | h280
                · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
                  · linarith only [h260, h281, hc03, hlam, hphi, u3elo1]
                  · linarith only [h128, h259, h280, h281, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h257, h259, h279, h280, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h285 | h285
                · rcases m.htr 1 3 4 (by decide) (by decide) with h286 | h286
                  · linarith only [h260, h286, hc03, hlam, hphi, u3elo1]
                  · linarith only [h128, h259, h285, h286, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                · linarith only [h128, h259, h278, h285, hlam]
            · linarith only [h0, h278, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h291 | h291
          · rcases m.htr 1 2 3 (by decide) (by decide) with h292 | h292
            · rcases m.htr 1 2 4 (by decide) (by decide) with h293 | h293
              · rcases m.htr 1 2 5 (by decide) (by decide) with h294 | h294
                · rcases m.htr 1 3 4 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h297 | h297
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h298 | h298
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h299 | h299
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h300 | h300
                            · linarith only [h291, h300, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                            · linarith only [h292, h298, h299, h300, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · linarith only [h295, h297, h299, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi2]
                        · linarith only [h128, h291, h298, hc23, hlam, hphi, u3elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h305 | h305
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h306 | h306
                          · linarith only [h293, h297, h306, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h308 | h308
                            · linarith only [h128, h291, h297, h308, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi1]
                            · rcases h1bigk with h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c | h310c
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h0, hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h128, hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h257, hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h259, hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                rcases p310_3 (m.d 0 1) (by simp) with h316 | h316
                                · linarith only [h316, hlam, p310_0]
                                · rcases p310_3 (m.d 1 2) (by simp) with h318 | h318
                                  · rcases p310_3 (m.d 1 3) (by simp) with h319 | h319
                                    · linarith only [h292, h319, hlam]
                                    · linarith only [h128, h319, hlam]
                                  · linarith only [h318, hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h128, h291, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p310_1, u4ehi3]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h257, hc01, hc12, hlam, hphi, p310_1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h257, h297, hc01, hc12, hlam, hphi, p310_1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, p310_1, u3elo1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h292, hlam, p310_1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h257, hc01, hlam, hphi, ht12, ht23, p310_1, u3elo1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h257, h297, hc01, hlam, hphi, ht12, ht23, p310_1, u3elo1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h297, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p310_1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h293, hlam, p310_1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h295, hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h297, hlam, p310_1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h296, hc01, hlam, hphi, ht12, ht23, p310_1, u3elo1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h294, hlam, p310_1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h296, hlam, p310_0]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [h296, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p310_1, u3elo1, u4ehi1]
                              · have p310_0 := h310c.1
                                have p310_1 := h310c.2.1
                                have p310_2 := h310c.2.2.1
                                have p310_3 := h310c.2.2.2
                                linarith only [hlam, p310_0]
                        · linarith only [h128, h291, h305, hc23, hlam, hphi, u3elo1]
                    · linarith only [h128, h291, h296, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                  · linarith only [h128, h291, h295, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
                    · linarith only [h292, h294, h346, hlam]
                    · linarith only [h128, h346, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h128, h291, h345, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h350 | h350
                · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
                  · linarith only [h292, h293, h351, hlam]
                  · linarith only [h128, h291, h351, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h354 | h354
                  · linarith only [h292, h293, h354, hlam]
                  · linarith only [h128, h291, h354, hlam]
            · linarith only [h0, h292, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
            · rcases m.htr 1 2 4 (by decide) (by decide) with h359 | h359
              · rcases m.htr 1 2 5 (by decide) (by decide) with h360 | h360
                · rcases m.htr 1 3 4 (by decide) (by decide) with h361 | h361
                  · linarith only [h291, h361, hc03, hlam, hphi, u3elo1]
                  · linarith only [h128, h361, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h364 | h364
                  · linarith only [h128, h291, h364, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h128, h364, hc01, hlam, hphi, ht12, ht23, u3elo3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h367 | h367
                · rcases m.htr 1 3 4 (by decide) (by decide) with h368 | h368
                  · linarith only [h128, h291, h368, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h128, h368, hc01, hlam, hphi, ht12, ht23, u3elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h371 | h371
                  · linarith only [h128, h291, h371, hc01, hlam, hphi, ht12, ht23, u3elo1]
                  · linarith only [h128, h371, hc01, hlam, hphi, ht12, ht23, u3elo3]
            · linarith only [h0, h358, hc01, hlam, hphi, ht12, ht23, u3elo2]

theorem r1l7_20_11_13_14_M_LI_L_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · linarith only [h1, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h8, hlam, hphi, ht34, u3ehi1, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                · linarith only [h1, h11, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h11, hlam, hphi, ht34, u3ehi1, u4elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h14 | h14
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
                · linarith only [h1, h15, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h15, hlam, hphi, ht34, u3ehi1, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                · linarith only [h1, h18, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h18, hlam, hphi, ht34, u3ehi1, u4elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
          · linarith only [h0, h21, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
            · rcases m.htr 1 2 5 (by decide) (by decide) with h24 | h24
              · linarith only [h1, h21, h24, h3, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                · linarith only [h1, h24, h26, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h26, hlam, hphi, ht34, u3ehi1, u4elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
              · linarith only [h1, h23, h29, h3, hlam, hphi, ht34, u3ehi1, u4elo2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                · linarith only [h1, h31, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h31, hlam, hphi, ht34, u3ehi1, u4elo3]
      · linarith only [h1, h2, hlam, hphi, ht34, u3ehi0, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h35 | h35
      · rcases m.htr 0 1 5 (by decide) (by decide) with h36 | h36
        · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
          · linarith only [h0, h37, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
            · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
              · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                      · linarith only [h0, h1, h37, h39, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h0, h1, h37, h44, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h41, h43, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h0, h1, h42, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h0, h1, h39, h41, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                · rcases m.htr 1 3 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h52 | h52
                    · linarith only [h39, h40, h52, hlam]
                    · linarith only [h50, h52, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h1, h36, h39, h40, h50, h51, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h36, h40, h50, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h57 | h57
              · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                  · linarith only [h39, h57, h59, hlam, hphi, ht34, u3ehi4, u4elo2]
                  · linarith only [h0, h1, h59, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h35, h39, h57, h58, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h66 | h66
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h67 | h67
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h68 | h68
                          · rcases h1bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h1, h37, hc12, hc23, hlam, hphi, p69_1]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h1, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h1, h37, h64, h65, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p69_1, u3ehi4]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h1, h37, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p69_1, u3ehi4]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h0, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h37, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h39, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h57, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h0, h37, hc12, hc23, hlam, hphi, p69_1]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              rcases p69_3 (m.d 0 1) (by simp) with h81 | h81
                              · linarith only [h1, h81, hlam]
                              · linarith only [h0, h81, hlam]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              rcases p69_3 (m.d 0 1) (by simp) with h85 | h85
                              · linarith only [h1, h85, hlam]
                              · linarith only [h35, h85, hlam]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              rcases p69_3 (m.d 0 1) (by simp) with h88 | h88
                              · linarith only [h1, h88, hlam]
                              · linarith only [h36, h88, hlam]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h35, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h35, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p69_1, u0elo0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h63, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h1, h35, h37, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p69_1, u3ehi4]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h36, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h1, h36, h37, hc12, hc23, hlam, hphi, p69_1]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h64, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [h65, hlam, p69_0]
                            · have p69_0 := h69c.1
                              have p69_1 := h69c.2.1
                              have p69_2 := h69c.2.2.1
                              have p69_3 := h69c.2.2.2
                              linarith only [hlam, p69_0]
                          · linarith only [h68, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h1, h35, h37, h65, h67, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h1, h35, h37, h65, h66, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h63, h65, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h1, h35, h63, h64, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h63, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
          · linarith only [h0, h107, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
            · rcases m.htr 1 2 5 (by decide) (by decide) with h110 | h110
              · linarith only [h0, h110, h36, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h114 | h114
                    · linarith only [h0, h114, h36, hc12, hlam, hphi, ht23, ht34, u4elo1]
                    · linarith only [h112, h114, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h0, h1, h109, h112, h113, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h1, h112, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h119 | h119
              · linarith only [h109, h119, h35, h36, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h121 | h121
                · rcases m.htr 1 3 5 (by decide) (by decide) with h122 | h122
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h123 | h123
                    · linarith only [h123, h35, h36, hlam]
                    · linarith only [h121, h123, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h1, h121, h122, h35, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1, h121, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
      · linarith only [h0, h35, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h129 | h129
    · rcases m.htr 0 1 4 (by decide) (by decide) with h130 | h130
      · rcases m.htr 0 1 5 (by decide) (by decide) with h131 | h131
        · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
          · rcases m.htr 1 2 4 (by decide) (by decide) with h133 | h133
            · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
              · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                · linarith only [h129, h135, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h135, hlam, hphi, ht34, u3ehi1, u4elo3]
              · linarith only [h0, h129, h132, h134, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h129, h132, h133, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h0, h129, h132, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h141 | h141
          · rcases m.htr 1 2 4 (by decide) (by decide) with h142 | h142
            · rcases m.htr 1 2 5 (by decide) (by decide) with h143 | h143
              · rcases m.htr 1 3 4 (by decide) (by decide) with h144 | h144
                · linarith only [h129, h144, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h144, hlam, hphi, ht34, u3ehi1, u4elo3]
              · linarith only [h0, h129, h141, h143, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h129, h141, h142, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h0, h129, h141, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h129, h130, hlam, hphi, ht34, u3ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h151 | h151
      · rcases m.htr 0 1 5 (by decide) (by decide) with h152 | h152
        · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
          · rcases m.htr 1 2 4 (by decide) (by decide) with h154 | h154
            · rcases m.htr 1 2 5 (by decide) (by decide) with h155 | h155
              · rcases m.htr 1 3 4 (by decide) (by decide) with h156 | h156
                · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h158 | h158
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h159 | h159
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h160 | h160
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                          · rcases h1bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h0, hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h129, hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h154, h159, h161, hlam, hphi, ht0b, ht34, ht45, ht5b, p162_1, u0elo0, u3ehi4]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h129, h153, h157, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p162_1, u3ehi4]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h151, h154, h159, h161, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p162_1, u3ehi4]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h129, hc01, hc12, hlam, hphi, p162_1]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              rcases p162_3 (m.d 0 1) (by simp) with h171 | h171
                              · linarith only [h0, h171, hlam]
                              · linarith only [h151, h171, hlam]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              rcases p162_3 (m.d 0 1) (by simp) with h174 | h174
                              · linarith only [h0, h174, hlam]
                              · linarith only [h152, h174, hlam]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h151, h154, h159, h161, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p162_1, u3ehi4]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h153, hlam, p162_1]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              rcases p162_3 (m.d 0 1) (by simp) with h180 | h180
                              · linarith only [h129, h180, hlam]
                              · linarith only [h151, h180, hlam]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              rcases p162_3 (m.d 0 1) (by simp) with h183 | h183
                              · linarith only [h129, h183, hlam]
                              · linarith only [h152, h183, hlam]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h151, hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h154, hlam, p162_1]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h156, hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h151, h157, hlam, hphi, ht0b, ht34, ht45, ht5b, p162_1, u0elo0, u3ehi4]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h152, hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h155, hlam, p162_1]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h157, hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [h158, hlam, p162_0]
                            · have p162_0 := h162c.1
                              have p162_1 := h162c.2.1
                              have p162_2 := h162c.2.2.1
                              have p162_3 := h162c.2.2.2
                              linarith only [hlam, p162_0]
                          · linarith only [h161, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h129, h151, h153, h158, h159, h160, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h159, hlam, hphi, ht34, u3ehi2, u4elo3]
                    · linarith only [h156, h158, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h129, h151, h156, h157, hc35, hlam, hphi, u3ehi3]
                · linarith only [h129, h151, h154, h156, hc24, hlam, hphi, u4elo3]
              · linarith only [h0, h152, h155, hlam]
            · linarith only [h129, h153, h154, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h204 | h204
            · rcases m.htr 1 2 5 (by decide) (by decide) with h205 | h205
              · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                · linarith only [h0, h151, h153, h206, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h153, h206, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h0, h152, h205, hlam]
            · linarith only [h0, h204, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h211 | h211
          · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
            · rcases m.htr 1 2 5 (by decide) (by decide) with h213 | h213
              · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                · rcases m.htr 1 3 5 (by decide) (by decide) with h215 | h215
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h216 | h216
                    · linarith only [h151, h152, h216, hlam]
                    · linarith only [h214, h216, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h129, h151, h214, h215, hc35, hlam, hphi, u3ehi3]
                · linarith only [h129, h214, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                · linarith only [h0, h151, h213, h221, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h129, h221, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h211, h212, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h225 | h225
            · rcases m.htr 1 2 5 (by decide) (by decide) with h226 | h226
              · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                · linarith only [h151, h152, h211, h226, h227, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h152, h211, h226, h227, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h230 | h230
                · linarith only [h0, h151, h211, h230, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h211, h230, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
            · linarith only [h0, h151, h225, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h234 | h234
        · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
          · rcases m.htr 1 2 4 (by decide) (by decide) with h236 | h236
            · rcases m.htr 1 2 5 (by decide) (by decide) with h237 | h237
              · rcases m.htr 1 3 4 (by decide) (by decide) with h238 | h238
                · rcases m.htr 1 3 5 (by decide) (by decide) with h239 | h239
                  · linarith only [h151, h234, h239, hlam, hphi, ht34, u3ehi4, u4elo1]
                  · linarith only [h238, h239, hc35, hlam, hphi, u3ehi3]
                · linarith only [h238, hlam, hphi, ht34, u3ehi1, u4elo3]
              · linarith only [h151, h234, h235, h237, hlam, hphi, ht34, u3ehi2, u4elo1]
            · linarith only [h235, h236, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h245 | h245
            · rcases m.htr 1 2 5 (by decide) (by decide) with h246 | h246
              · rcases m.htr 1 3 4 (by decide) (by decide) with h247 | h247
                · rcases m.htr 1 3 5 (by decide) (by decide) with h248 | h248
                  · linarith only [h151, h234, h248, hlam, hphi, ht34, u3ehi4, u4elo1]
                  · linarith only [h247, h248, hc35, hlam, hphi, u3ehi3]
                · linarith only [h151, h235, h245, h247, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
              · linarith only [h151, h234, h245, h246, hlam]
            · linarith only [h0, h234, h245, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
          · rcases m.htr 1 2 4 (by decide) (by decide) with h255 | h255
            · rcases m.htr 1 2 5 (by decide) (by decide) with h256 | h256
              · rcases m.htr 1 3 4 (by decide) (by decide) with h257 | h257
                · rcases m.htr 1 3 5 (by decide) (by decide) with h258 | h258
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h259 | h259
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h260 | h260
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h261 | h261
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h262 | h262
                          · rcases h1bigk with h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h0, hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h129, hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h151, hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h234, hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              rcases p263_3 (m.d 0 1) (by simp) with h269 | h269
                              · linarith only [h269, hlam, p263_0]
                              · rcases p263_3 (m.d 1 2) (by simp) with h271 | h271
                                · rcases p263_3 (m.d 1 3) (by simp) with h272 | h272
                                  · linarith only [h254, h272, hlam]
                                  · linarith only [h129, h272, hlam]
                                · linarith only [h271, hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h254, h260, h262, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p263_1, u3ehi4]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h234, h259, hc01, hc12, hlam, hphi, p263_1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h234, hc01, hc12, hlam, hphi, p263_1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              rcases p263_3 (m.d 0 1) (by simp) with h280 | h280
                              · linarith only [h280, hlam, p263_0]
                              · rcases p263_3 (m.d 1 2) (by simp) with h282 | h282
                                · rcases p263_3 (m.d 1 3) (by simp) with h283 | h283
                                  · rcases p263_3 (m.d 1 4) (by simp) with h284 | h284
                                    · linarith only [h257, h284, hlam]
                                    · linarith only [h151, h284, hlam]
                                  · linarith only [h283, hlam, p263_0]
                                · linarith only [h0, h282, hlam]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h254, hlam, p263_1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h234, h259, hc01, hc13, hlam, hphi, p263_1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h234, h254, hc01, hc12, hlam, hphi, p263_1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p263_1, u4elo1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h255, hlam, p263_1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h257, hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h234, hc01, hlam, hphi, ht12, ht23, ht34, p263_1, u4elo1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h259, hc01, hlam, hphi, ht12, ht23, ht34, p263_1, u4elo1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h256, hlam, p263_1]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h258, hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [h259, hlam, p263_0]
                            · have p263_0 := h263c.1
                              have p263_1 := h263c.2.1
                              have p263_2 := h263c.2.2.1
                              have p263_3 := h263c.2.2.2
                              linarith only [hlam, p263_0]
                          · linarith only [h262, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h259, h261, hc24, hlam, hphi, u4elo1]
                      · linarith only [h260, hlam, hphi, ht34, u3ehi2, u4elo3]
                    · linarith only [h257, h259, hlam, hphi, ht34, u3ehi3, u4elo4]
                  · linarith only [h257, h258, hc35, hlam, hphi, u3ehi3]
                · linarith only [h257, hlam, hphi, ht34, u3ehi1, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h309 | h309
                · rcases m.htr 1 3 5 (by decide) (by decide) with h310 | h310
                  · linarith only [h254, h256, h310, hlam]
                  · linarith only [h309, h310, hc35, hlam, hphi, u3ehi3]
                · linarith only [h309, hlam, hphi, ht34, u3ehi1, u4elo3]
            · linarith only [h0, h255, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
            · rcases m.htr 1 2 5 (by decide) (by decide) with h316 | h316
              · rcases m.htr 1 3 4 (by decide) (by decide) with h317 | h317
                · rcases m.htr 1 3 5 (by decide) (by decide) with h318 | h318
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h321 | h321
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h322 | h322
                          · rcases h1bigk with h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c | h323c
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h0, hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h129, hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h151, hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h234, hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h254, hc01, hc23, hlam, hphi, ht12, p323_1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h254, hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h234, h254, h319, hc01, hc23, hlam, hphi, ht12, p323_1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h234, h254, hc01, hc23, hlam, hphi, ht12, p323_1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              rcases p323_3 (m.d 0 1) (by simp) with h334 | h334
                              · linarith only [h334, hlam, p323_0]
                              · rcases p323_3 (m.d 1 2) (by simp) with h336 | h336
                                · linarith only [h254, h336, hlam]
                                · linarith only [h0, h336, hlam]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h315, h320, h322, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p323_1, u3ehi4]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h234, h254, h319, hc01, hc23, hlam, hphi, ht12, p323_1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h234, h254, hc01, hc23, hlam, hphi, ht12, p323_1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p323_1, u4elo1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h315, hlam, p323_1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h317, hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h234, h254, h315, h320, h322, hc01, hc23, hlam, hphi, ht12, ht34, p323_1, u3ehi4, u4elo1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h254, h316, hc01, hc23, hlam, hphi, ht12, p323_1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h316, hlam, p323_1]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h318, hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [h319, hlam, p323_0]
                            · have p323_0 := h323c.1
                              have p323_1 := h323c.2.1
                              have p323_2 := h323c.2.2.1
                              have p323_3 := h323c.2.2.2
                              linarith only [hlam, p323_0]
                          · linarith only [h322, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h319, h321, hc24, hlam, hphi, u4elo1]
                      · linarith only [h254, h320, hc12, hlam, hphi, ht23, ht34, u4elo3]
                    · linarith only [h151, h319, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h317, h318, hc35, hlam, hphi, u3ehi3]
                · linarith only [h317, hlam, hphi, ht34, u3ehi1, u4elo3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h359 | h359
                · rcases m.htr 1 3 5 (by decide) (by decide) with h360 | h360
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h361 | h361
                    · linarith only [h315, h316, h361, hlam]
                    · linarith only [h151, h361, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h359, h360, hc35, hlam, hphi, u3ehi3]
                · linarith only [h359, hlam, hphi, ht34, u3ehi1, u4elo3]
            · linarith only [h0, h315, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]

end R2N4
