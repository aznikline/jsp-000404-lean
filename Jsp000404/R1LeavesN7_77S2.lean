import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_0_L_0_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h5, h8, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h0, h5, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h2, h4, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                · linarith only [h12, h2, h3, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                  · linarith only [h14, h2, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h12, h16, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                      · rcases h3bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19_1, u2elo0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19_1, u2elo0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h12, h18, h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19_1, u2elo0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h12, h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19_1, u2elo0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h1, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h12, h18, hc23, hc34, hlam, hphi, p19_1]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h6, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h12, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h2, hlam, p19_0]
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
                          linarith only [h14, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h16, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h3, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h2, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19_1, u2elo0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19_1, u2elo0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h12, h2, h3, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p19_1, u2elo0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h4, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h5, hc23, hc35, hlam, hphi, p19_1]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19_1, u2elo0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h18, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [hlam, p19_0]
                      · rcases h3bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u2elo0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u2elo0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h14, h2, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p45_1, u2elo0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h16, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p45_1, u2elo0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h1, hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p45_1, u0elo0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h6, hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h12, hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h2, hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h5, hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h14, hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h16, hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h3, hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [hc13, hc34, hlam, hphi, p45_1]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h2, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u2elo0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h18, hlam, p45_1]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h4, hlam, p45_0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [hc13, hc35, hlam, hphi, p45_1]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u2elo0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [h2, h4, h6, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p45_1, u2elo0]
                        · have p45_0 := h45c.1
                          have p45_1 := h45c.2.1
                          have p45_2 := h45c.2.2.1
                          have p45_3 := h45c.2.2.2
                          linarith only [hlam, p45_0]
            · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
            · rcases m.htr 1 3 4 (by decide) (by decide) with h73 | h73
              · rcases m.htr 1 3 5 (by decide) (by decide) with h74 | h74
                · linarith only [h1, h4, h74, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                  · linarith only [h0, h72, h76, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h1, h4, h73, h76, hc23, hc35, hlam, hphi]
              · linarith only [h3, h4, h73, hc13, hc35, hlam, hphi]
            · linarith only [h2, h72, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h81 | h81
          · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
            · rcases m.htr 1 3 4 (by decide) (by decide) with h83 | h83
              · linarith only [h1, h3, h83, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h85 | h85
                · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                  · linarith only [h1, h3, h82, h85, h86, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                    · linarith only [h0, h82, h88, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1, h3, h85, h88, hc23, hc34, hlam, hphi]
                · linarith only [h3, h81, h85, hc13, hc34, hlam, hphi]
            · linarith only [h2, h82, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
            · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
              · linarith only [h1, h3, h94, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h96 | h96
                · linarith only [h1, h81, h96, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h98 | h98
                  · linarith only [h1, h3, h93, h98, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h100 | h100
                    · linarith only [h1, h100, h81, h93, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h102 | h102
                      · rcases h3bigk with h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c | h103c
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h93, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p103_1, u0elo2]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h102, h81, hc23, hc34, hlam, hphi, p103_1]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h3, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h81, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h1, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p103_1, u0elo0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h94, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h96, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h2, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h93, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h98, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h100, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [hc03, hc34, hlam, hphi, p103_1]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h93, hc23, hc34, hlam, hphi, p103_1]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p103_1]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h1, h81, h93, hc23, hc34, hlam, hphi, p103_1]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h1, h93, hc23, hc35, hlam, hphi, p103_1]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h93, hc23, hc35, hlam, hphi, p103_1]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [hc23, hc35, hlam, hphi, p103_1]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [h102, hlam, p103_0]
                        · have p103_0 := h103c.1
                          have p103_1 := h103c.2.1
                          have p103_2 := h103c.2.2.1
                          have p103_3 := h103c.2.2.2
                          linarith only [hlam, p103_0]
                      · rcases h3bigk with h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c | h129c
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h93, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p129_1, u0elo2]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p129_1, u2elo0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h3, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h81, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h1, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p129_1, u0elo0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h94, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h96, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h2, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h93, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h98, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h100, hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h102, hc03, hc45, hlam, hphi, ht34, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h102, hc13, hc45, hlam, hphi, ht34, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h102, hc23, hc45, hlam, hphi, ht34, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h102, hlam, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h102, hc03, hc45, hlam, hphi, ht34, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h102, h93, hc23, hc45, hlam, hphi, ht34, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h102, hc23, hc45, hlam, hphi, ht34, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [h102, h3, hc04, hc45, hlam, hphi, p129_1]
                        · have p129_0 := h129c.1
                          have p129_1 := h129c.2.1
                          have p129_2 := h129c.2.2.1
                          have p129_3 := h129c.2.2.2
                          linarith only [hlam, p129_0]
            · linarith only [h2, h93, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h156 | h156
        · rcases m.htr 0 3 5 (by decide) (by decide) with h157 | h157
          · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
            · linarith only [h0, h158, h2, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
              · rcases m.htr 1 3 5 (by decide) (by decide) with h161 | h161
                · rcases m.htr 2 3 4 (by decide) (by decide) with h162 | h162
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h164 | h164
                      · linarith only [h1, h160, h164, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases h3bigk with h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c | h166c
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p166_1, u0elo2]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h2, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p166_1, u2elo2]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h164, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p166_1, u2elo2]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h1, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h158, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1, u0elo0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h1, h164, hc34, hlam, hphi, ht0b, ht45, ht5b, p166_1, u0elo0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p166_1, u2elo2]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p166_1, u2elo2]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p166_1, u2elo2]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h164, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p166_1, u2elo2]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h156, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h160, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h162, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h164, hlam, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h157, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h161, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h163, hlam, p166_0]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [h161, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p166_1]
                        · have p166_0 := h166c.1
                          have p166_1 := h166c.2.1
                          have p166_2 := h166c.2.2.1
                          have p166_3 := h166c.2.2.2
                          linarith only [hlam, p166_0]
                    · linarith only [h1, h161, h163, h2, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h156, h162, h2, hlam]
                · linarith only [h157, h160, h161, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h156, h158, h160, h2, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h196 | h196
            · linarith only [h0, h156, h196, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
              · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                · linarith only [h1, h157, h199, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h201 | h201
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h202 | h202
                    · linarith only [h1, h157, h198, h202, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h1, h198, h204, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · rcases h3bigk with h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c | h206c
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h157, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p206_1, u0elo4]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h2, hlam, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h2, h202, h204, hc34, hc45, hlam, hphi, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h157, hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h1, hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h196, hlam, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p206_1, u0elo0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h199, hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h202, h204, hc03, hc45, hlam, hphi, ht34, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h202, h204, hc13, hc45, hlam, hphi, ht34, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h202, h204, hc34, hc45, hlam, hphi, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h202, hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h156, hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h198, hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h201, hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [hlam, p206_0]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h204, hlam, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h204, hc03, hc45, hlam, hphi, ht34, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h198, h204, hc34, hc45, hlam, hphi, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h2, h204, hc02, hc45, hlam, hphi, ht23, ht34, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [h204, hc34, hc45, hlam, hphi, p206_1]
                        · have p206_0 := h206c.1
                          have p206_1 := h206c.2.1
                          have p206_2 := h206c.2.2.1
                          have p206_3 := h206c.2.2.2
                          linarith only [hlam, p206_0]
                  · linarith only [h0, h1, h198, h2, h201, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h156, h157, h198, hc13, hc35, hlam, hphi]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h234 | h234
          · rcases m.htr 1 2 3 (by decide) (by decide) with h235 | h235
            · linarith only [h0, h2, h234, h235, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h237 | h237
              · linarith only [h1, h156, h234, h237, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h239 | h239
                · rcases m.htr 2 3 4 (by decide) (by decide) with h240 | h240
                  · linarith only [h1, h156, h239, h240, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h242 | h242
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h243 | h243
                      · rcases h3bigk with h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h239, h243, hc45, hlam, hphi, ht0b, ht5b, p244_1, u0elo2]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h2, hlam, p244_1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h156, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h243, hc45, hlam, hphi, ht0b, ht5b, p244_1, u0elo2]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h1, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h235, hlam, p244_1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h237, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h1, h243, hc45, hlam, hphi, ht0b, ht5b, p244_1, u0elo0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h240, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p244_1, u2elo3]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h240, hc13, hc34, hlam, hphi, p244_1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h240, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h240, h243, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p244_1, u2elo3]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h2, hc02, hc34, hlam, hphi, ht23, p244_1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h239, h243, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p244_1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p244_1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          rcases p244_3 (m.d 0 3) (by simp) with h264 | h264
                          · linarith only [h156, h264, hlam]
                          · linarith only [h234, h264, hlam]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h234, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h239, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h242, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h243, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                      · linarith only [h0, h2, h240, h243, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h1, h2, h239, h242, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · linarith only [h156, h234, h239, hc13, hc34, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h275 | h275
            · linarith only [h0, h2, h275, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
              · linarith only [h1, h156, h277, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                · linarith only [h0, h1, h2, h234, h279, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                  · linarith only [h0, h156, h2, h281, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
                    · linarith only [h0, h2, h234, h283, hc12, hlam, hphi, u2elo2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h285 | h285
                      · rcases h3bigk with h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c | h286c
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p286_1, u0elo2]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h2, hlam, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h156, hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h234, hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h1, hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h275, hlam, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h277, hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h279, hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p286_1, u2elo2]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h283, hc13, hc35, hlam, hphi, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h281, hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h283, hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h0, h2, hc12, hc34, hlam, hphi, ht23, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h275, hc12, hc34, hlam, hphi, ht23, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h0, h2, h234, hc12, hc34, hlam, hphi, ht23, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h0, h2, hc12, hc35, hlam, hphi, ht23, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h275, hc12, hc35, hlam, hphi, ht23, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h0, h2, hc12, hc35, hlam, hphi, ht23, p286_1]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [h285, hlam, p286_0]
                        · have p286_0 := h286c.1
                          have p286_1 := h286c.2.1
                          have p286_2 := h286c.2.2.1
                          have p286_3 := h286c.2.2.2
                          linarith only [hlam, p286_0]
                      · linarith only [h0, h2, h281, h285, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
      · linarith only [h0, h1, h313, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
        · rcases m.htr 0 3 5 (by decide) (by decide) with h316 | h316
          · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
            · linarith only [h313, h317, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h1, h317, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h320 | h320
            · linarith only [h0, h1, h316, h320, hc23, hc35, hlam, hphi]
            · linarith only [h0, h1, h320, hc12, hlam, hphi, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h323 | h323
          · rcases m.htr 1 2 3 (by decide) (by decide) with h324 | h324
            · linarith only [h0, h1, h315, h324, hc23, hc34, hlam, hphi]
            · linarith only [h0, h1, h324, hc12, hlam, hphi, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h327 | h327
            · linarith only [h0, h1, h315, h327, hc23, hc34, hlam, hphi]
            · linarith only [h0, h1, h327, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h330 | h330
    · rcases m.htr 0 2 3 (by decide) (by decide) with h331 | h331
      · rcases m.htr 0 3 4 (by decide) (by decide) with h332 | h332
        · rcases m.htr 0 3 5 (by decide) (by decide) with h333 | h333
          · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
            · rcases m.htr 1 3 4 (by decide) (by decide) with h335 | h335
              · linarith only [h0, h330, h335, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h0, h330, h332, h334, h335, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
            · linarith only [h0, h334, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
            · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
              · linarith only [h0, h330, h340, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · linarith only [h332, h333, h340, hc13, hc35, hlam, hphi]
            · linarith only [h0, h339, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h344 | h344
          · rcases m.htr 1 2 3 (by decide) (by decide) with h345 | h345
            · rcases m.htr 1 3 4 (by decide) (by decide) with h346 | h346
              · linarith only [h330, h332, h346, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                · linarith only [h0, h330, h348, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h332, h344, h345, h348, hc23, hc34, hlam, hphi]
            · linarith only [h0, h345, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
            · rcases m.htr 1 3 4 (by decide) (by decide) with h353 | h353
              · linarith only [h0, h330, h353, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h355 | h355
                · linarith only [h330, h344, h355, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                  · linarith only [h0, h331, h332, h357, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h359 | h359
                    · linarith only [h330, h344, h352, h359, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h361 | h361
                      · rcases h3bigk with h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h352, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p362_1, u0elo2]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h0, h330, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p362_1, u2elo1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h332, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h344, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h330, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h0, h330, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p362_1, u2elo1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h353, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h355, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h331, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h352, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h357, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h359, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hc03, hc34, hlam, hphi, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h352, hc23, hc34, hlam, hphi, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h330, h344, h352, hc23, hc34, hlam, hphi, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h330, h352, hc23, hc35, hlam, hphi, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h352, hc23, hc35, hlam, hphi, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hc23, hc35, hlam, hphi, p362_1]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [h361, hlam, p362_0]
                        · have p362_0 := h362c.1
                          have p362_1 := h362c.2.1
                          have p362_2 := h362c.2.2.1
                          have p362_3 := h362c.2.2.2
                          linarith only [hlam, p362_0]
                      · rcases h3bigk with h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c | h388c
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h352, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p388_1, u0elo2]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h0, h330, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p388_1, u2elo1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h332, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h344, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h330, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h0, h330, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p388_1, u2elo1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h353, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h355, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h331, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h352, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h357, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h359, hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h361, hc03, hc45, hlam, hphi, ht34, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h361, hc13, hc45, hlam, hphi, ht34, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h361, hc23, hc45, hlam, hphi, ht34, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h361, hlam, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h330, h352, h361, hc23, hc45, hlam, hphi, ht34, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h352, h361, hc23, hc45, hlam, hphi, ht34, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h361, hc23, hc45, hlam, hphi, ht34, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [h332, h361, hc04, hc45, hlam, hphi, p388_1]
                        · have p388_0 := h388c.1
                          have p388_1 := h388c.2.1
                          have p388_2 := h388c.2.2.1
                          have p388_3 := h388c.2.2.2
                          linarith only [hlam, p388_0]
            · linarith only [h0, h352, hc01, hlam, hphi, ht12, u2elo2]
      · linarith only [h0, h330, h331, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h416 | h416
      · rcases m.htr 0 3 4 (by decide) (by decide) with h417 | h417
        · rcases m.htr 0 3 5 (by decide) (by decide) with h418 | h418
          · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
            · rcases m.htr 1 3 4 (by decide) (by decide) with h420 | h420
              · rcases m.htr 1 3 5 (by decide) (by decide) with h421 | h421
                · rcases m.htr 2 3 4 (by decide) (by decide) with h422 | h422
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h423 | h423
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h424 | h424
                      · linarith only [h416, h422, h424, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases h3bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h330, hlam, p426_1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p426_1, u0elo2]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h0, h416, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p426_1, u2elo1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h0, h416, h424, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p426_1, u2elo1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h330, hc01, hc13, hlam, hphi, p426_1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h419, h423, h424, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p426_1, u2elo1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h419, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p426_1, u2elo1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h419, h424, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p426_1, u2elo1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h416, hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h419, hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h416, hc34, hlam, hphi, ht0b, ht45, ht5b, p426_1, u0elo2]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h0, h416, h424, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p426_1, u2elo1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h417, hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h420, hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h422, hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h424, hlam, p426_1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h418, hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h421, hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h423, hlam, p426_0]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [h330, h418, h419, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p426_1, u2elo1]
                        · have p426_0 := h426c.1
                          have p426_1 := h426c.2.1
                          have p426_2 := h426c.2.2.1
                          have p426_3 := h426c.2.2.2
                          linarith only [hlam, p426_0]
                    · linarith only [h330, h418, h419, h422, h423, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h453 | h453
                    · linarith only [h330, h417, h419, h422, h453, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h455 | h455
                      · rcases h3bigk with h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c | h456c
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h330, hlam, p456_1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h330, h419, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p456_1, u2elo1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h330, h419, h453, h455, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p456_1, u2elo1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h330, h419, h453, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p456_1, u2elo1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h419, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p456_1, u2elo1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h419, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p456_1, u2elo1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h419, h455, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p456_1, u2elo1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h419, h453, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p456_1, u2elo1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h416, hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h419, hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h422, hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h453, hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h417, hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h420, hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h417, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p456_1, u0elo2]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h330, h417, h419, h453, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p456_1, u2elo1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h418, hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h421, hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [hc23, hc35, hlam, hphi, p456_1]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [h455, hlam, p456_0]
                        · have p456_0 := h456c.1
                          have p456_1 := h456c.2.1
                          have p456_2 := h456c.2.2.1
                          have p456_3 := h456c.2.2.2
                          linarith only [hlam, p456_0]
                      · rcases h3bigk with h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c | h482c
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h330, hlam, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h330, h419, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p482_1, u2elo1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h330, h419, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p482_1, u2elo1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h330, h419, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p482_1, u2elo1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h419, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p482_1, u2elo1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h419, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p482_1, u2elo1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h419, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p482_1, u2elo1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h419, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p482_1, u2elo1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h416, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h419, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h422, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h453, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h417, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h420, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h417, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p482_1, u0elo2]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h455, hlam, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h418, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h421, hlam, p482_0]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hc23, hc35, hlam, hphi, p482_1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [h330, h418, h419, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p482_1, u2elo1]
                        · have p482_0 := h482c.1
                          have p482_1 := h482c.2.1
                          have p482_2 := h482c.2.2.1
                          have p482_3 := h482c.2.2.2
                          linarith only [hlam, p482_0]
                · linarith only [h330, h418, h421, hlam]
              · linarith only [h330, h417, h420, hlam]
            · linarith only [h0, h419, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
            · rcases m.htr 1 3 4 (by decide) (by decide) with h512 | h512
              · rcases m.htr 1 3 5 (by decide) (by decide) with h513 | h513
                · linarith only [h417, h418, h511, h513, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h515 | h515
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h516 | h516
                    · linarith only [h416, h513, h516, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h518 | h518
                      · linarith only [h0, h416, h515, h518, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases h3bigk with h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c | h520c
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h330, hlam, p520_1]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h418, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p520_1, u0elo4]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p520_1, u0elo2]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h418, hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h513, hc03, hc35, hlam, hphi, p520_1]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h513, h515, h518, hc34, hc45, hlam, hphi, p520_1]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h513, h518, hc34, hc45, hlam, hphi, p520_1]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h513, hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h416, hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h511, hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h416, hc34, hlam, hphi, ht0b, ht45, ht5b, p520_1, u0elo2]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h516, hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h417, hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h512, hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h515, hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [hlam, p520_0]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h518, hlam, p520_1]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h518, hc03, hc45, hlam, hphi, ht34, p520_1]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h518, hc13, hc45, hlam, hphi, ht34, p520_1]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h515, h518, hc34, hc45, hlam, hphi, p520_1]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [h518, hc34, hc45, hlam, hphi, p520_1]
                        · have p520_0 := h520c.1
                          have p520_1 := h520c.2.1
                          have p520_2 := h520c.2.2.1
                          have p520_3 := h520c.2.2.2
                          linarith only [hlam, p520_0]
                  · linarith only [h417, h418, h515, hc23, hc35, hlam, hphi]
              · linarith only [h330, h417, h512, hlam]
            · linarith only [h0, h511, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h549 | h549
          · rcases m.htr 1 2 3 (by decide) (by decide) with h550 | h550
            · rcases m.htr 1 3 4 (by decide) (by decide) with h551 | h551
              · linarith only [h417, h549, h550, h551, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h553 | h553
                · rcases m.htr 2 3 4 (by decide) (by decide) with h554 | h554
                  · linarith only [h416, h551, h554, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h556 | h556
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h557 | h557
                      · rcases h3bigk with h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c | h558c
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h330, hlam, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h556, h557, hc45, hlam, hphi, ht0b, ht5b, p558_1, u0elo2]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h417, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h557, hc45, hlam, hphi, ht0b, ht5b, p558_1, u0elo2]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h551, hc03, hc34, hlam, hphi, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h551, h556, h557, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h551, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h551, h557, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h416, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h550, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h554, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h416, h557, hc45, hlam, hphi, ht0b, ht5b, p558_1, u0elo2]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hc03, hc34, hlam, hphi, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hc13, hc34, hlam, hphi, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p558_1]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          rcases p558_3 (m.d 0 3) (by simp) with h578 | h578
                          · linarith only [h417, h578, hlam]
                          · linarith only [h549, h578, hlam]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h549, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h553, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h556, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [h557, hlam, p558_0]
                        · have p558_0 := h558c.1
                          have p558_1 := h558c.2.1
                          have p558_2 := h558c.2.2.1
                          have p558_3 := h558c.2.2.2
                          linarith only [hlam, p558_0]
                      · linarith only [h330, h551, h557, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · linarith only [h330, h549, h551, h556, hc23, hc34, hlam, hphi]
                · linarith only [h330, h549, h553, hlam]
            · linarith only [h0, h550, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h590 | h590
            · rcases m.htr 1 3 4 (by decide) (by decide) with h591 | h591
              · linarith only [h330, h417, h590, h591, hc01, hlam, hphi, ht12, u2elo1]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h593 | h593
                · linarith only [h330, h549, h590, h593, hc01, hlam, hphi, ht12, u2elo1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h595 | h595
                  · linarith only [h330, h591, h595, hc01, hlam, hphi, ht12, u2elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h597 | h597
                    · linarith only [h0, h330, h416, h593, h597, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h599 | h599
                      · rcases h3bigk with h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c | h600c
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h330, hlam, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p600_1, u0elo2]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h417, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h549, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h593, hc03, hc35, hlam, hphi, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h593, hc23, hc35, hlam, hphi, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h591, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h593, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h416, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h590, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h595, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h597, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h330, hc01, hc34, hlam, hphi, ht12, ht23, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hc13, hc34, hlam, hphi, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hc23, hc34, hlam, hphi, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h330, h549, hc01, hc34, hlam, hphi, ht12, ht23, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h330, hc01, hc35, hlam, hphi, ht12, ht23, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h330, hc01, hc35, hlam, hphi, ht12, ht23, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hc23, hc35, hlam, hphi, p600_1]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [h599, hlam, p600_0]
                        · have p600_0 := h600c.1
                          have p600_1 := h600c.2.1
                          have p600_2 := h600c.2.2.1
                          have p600_3 := h600c.2.2.2
                          linarith only [hlam, p600_0]
                      · linarith only [h330, h591, h599, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h0, h590, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h628 | h628
        · rcases m.htr 0 3 5 (by decide) (by decide) with h629 | h629
          · rcases m.htr 1 2 3 (by decide) (by decide) with h630 | h630
            · linarith only [h416, h630, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h630, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h633 | h633
            · linarith only [h0, h416, h633, hc01, hlam, hphi, ht12, u2elo1]
            · linarith only [h0, h633, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h636 | h636
          · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
            · linarith only [h0, h416, h637, hc01, hlam, hphi, ht12, u2elo1]
            · linarith only [h0, h637, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h640 | h640
            · linarith only [h0, h416, h640, hc01, hlam, hphi, ht12, u2elo1]
            · linarith only [h0, h640, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
