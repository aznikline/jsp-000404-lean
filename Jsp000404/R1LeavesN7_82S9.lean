import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_LR_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · linarith only [h2, h4, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h1, h4, h8, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
              · linarith only [h0, h1, h10, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h1, h12, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                    · linarith only [h0, h15, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                    · linarith only [h12, h14, h15, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h18 | h18
                    · linarith only [h0, h18, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                      · linarith only [h12, h18, h20, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h12, h20, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
          · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
            · linarith only [h0, h24, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · linarith only [h2, h24, h3, hc12, hc25, hlam, hphi]
          · linarith only [h1, h23, h3, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h28 | h28
        · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
            · linarith only [h0, h2, h30, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h32 | h32
              · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                · linarith only [h0, h29, h33, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h0, h29, h35, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h0, h32, h37, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                    · linarith only [h1, h2, h37, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h2, h28, h32, hc12, hc24, hlam, hphi]
          · linarith only [h1, h2, h29, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
            · linarith only [h0, h2, h43, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h45 | h45
              · linarith only [h0, h1, h28, h45, hlam, hphi, u0ehi7, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                · linarith only [h0, h42, h47, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h49 | h49
                  · linarith only [h0, h42, h49, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h51 | h51
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h52 | h52
                      · rcases h2bigk with h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c | h53c
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h28, h47, h51, hc12, hc34, hlam, hphi, ht23, p53_1]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h28, h47, h51, hc23, hc34, hlam, hphi, p53_1]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h2, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h28, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h0, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h0, h1, h28, h47, h51, hc23, hc34, hlam, hphi, p53_1, u0ehi7, u0elo0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h43, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h45, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h1, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h42, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h47, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h49, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h1, h47, hc34, hlam, hphi, ht01, ht12, ht23, p53_1, u0ehi7]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h42, h47, hc23, hc34, hlam, hphi, p53_1]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          rcases p53_3 (m.d 0 2) (by simp) with h71 | h71
                          · linarith only [h2, h71, hlam]
                          · linarith only [h1, h71, hlam]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h1, h28, h47, hc34, hlam, hphi, ht01, ht12, ht23, p53_1, u0ehi7]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h1, hc25, hlam, hphi, ht01, ht12, p53_1, u0ehi7]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h42, h49, hc23, hc35, hlam, hphi, p53_1]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          rcases p53_3 (m.d 0 2) (by simp) with h78 | h78
                          · linarith only [h28, h78, hlam]
                          · linarith only [h1, h78, hlam]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [h51, hlam, p53_0]
                        · have p53_0 := h53c.1
                          have p53_1 := h53c.2.1
                          have p53_2 := h53c.2.2.1
                          have p53_3 := h53c.2.2.2
                          linarith only [hlam, p53_0]
                      · linarith only [h47, h51, h52, hlam]
                    · linarith only [h1, h2, h51, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
          · linarith only [h1, h2, h42, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h86 | h86
      · rcases m.htr 0 2 5 (by decide) (by decide) with h87 | h87
        · rcases m.htr 1 2 3 (by decide) (by decide) with h88 | h88
          · linarith only [h1, h86, h88, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h90 | h90
            · linarith only [h0, h90, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · linarith only [h1, h86, h90, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
          · linarith only [h1, h86, h93, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
            · linarith only [h0, h95, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
            · linarith only [h1, h86, h95, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h98 | h98
        · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
          · linarith only [h1, h99, hc12, hlam, hphi, ht01, u0ehi6]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
            · linarith only [h0, h101, h86, h98, hlam, hphi, u0ehi9, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
              · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                    · linarith only [h0, h103, h106, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                    · linarith only [h106, h86, h98, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi9]
                  · linarith only [h104, h105, h86, h98, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                · linarith only [h1, h104, h98, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
              · linarith only [h1, h103, h98, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
          · linarith only [h1, h112, hc12, hlam, hphi, ht01, u0ehi6]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
            · linarith only [h0, h114, h86, hlam, hphi, u0ehi6, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
              · linarith only [h0, h116, h98, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h120 | h120
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                      · rcases h2bigk with h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c | h122c
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h118, h120, h98, hc12, hc23, hlam, hphi, p122_1]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h1, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h86, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h98, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h0, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h112, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h114, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h116, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p122_1, u0ehi6]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          rcases p122_3 (m.d 0 2) (by simp) with h134 | h134
                          · linarith only [h1, h134, hlam]
                          · linarith only [h0, h134, hlam]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h86, hc23, hlam, hphi, ht01, ht12, p122_1, u0ehi6]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h98, hc23, hlam, hphi, ht01, ht12, p122_1, u0ehi6]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hc24, hlam, hphi, ht01, ht12, p122_1, u0ehi6]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          rcases p122_3 (m.d 0 2) (by simp) with h141 | h141
                          · linarith only [h141, h86, hlam]
                          · linarith only [h0, h141, hlam]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h118, hlam, p122_1]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h118, h98, hc23, hlam, hphi, ht01, ht12, p122_1, u0ehi6]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht12, p122_1, u0ehi6]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          rcases p122_3 (m.d 0 2) (by simp) with h148 | h148
                          · linarith only [h148, h98, hlam]
                          · linarith only [h0, h148, hlam]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h119, hlam, p122_1]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [h120, hlam, p122_0]
                        · have p122_0 := h122c.1
                          have p122_1 := h122c.2.1
                          have p122_2 := h122c.2.2.1
                          have p122_3 := h122c.2.2.2
                          linarith only [hlam, p122_0]
                      · rcases h2bigk with h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h1, hc12, hc23, hlam, hphi, p154_1]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h1, hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h86, hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h98, hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h0, hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h112, hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h114, hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h116, hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p154_1, u0ehi6]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          rcases p154_3 (m.d 0 2) (by simp) with h166 | h166
                          · linarith only [h1, h166, hlam]
                          · linarith only [h0, h166, hlam]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h86, hc23, hlam, hphi, ht01, ht12, p154_1, u0ehi6]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h98, hc23, hlam, hphi, ht01, ht12, p154_1, u0ehi6]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [hc24, hlam, hphi, ht01, ht12, p154_1, u0ehi6]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          rcases p154_3 (m.d 0 2) (by simp) with h173 | h173
                          · linarith only [h173, h86, hlam]
                          · linarith only [h0, h173, hlam]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h118, hlam, p154_1]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h118, h98, hc23, hlam, hphi, ht01, ht12, p154_1, u0ehi6]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht12, p154_1, u0ehi6]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          rcases p154_3 (m.d 0 2) (by simp) with h180 | h180
                          · linarith only [h180, h98, hlam]
                          · linarith only [h0, h180, hlam]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h119, hlam, p154_1]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [h120, hlam, p154_0]
                        · have p154_0 := h154c.1
                          have p154_1 := h154c.2.1
                          have p154_2 := h154c.2.2.1
                          have p154_3 := h154c.2.2.2
                          linarith only [hlam, p154_0]
                    · linarith only [h120, h86, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                  · linarith only [h1, h119, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h1, h118, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h189 | h189
    · rcases m.htr 0 2 4 (by decide) (by decide) with h190 | h190
      · rcases m.htr 0 2 5 (by decide) (by decide) with h191 | h191
        · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
          · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
            · rcases m.htr 1 2 5 (by decide) (by decide) with h194 | h194
              · rcases m.htr 2 3 4 (by decide) (by decide) with h195 | h195
                · linarith only [h189, h195, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h197 | h197
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h198 | h198
                    · linarith only [h190, h198, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                    · linarith only [h195, h197, h198, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h201 | h201
                    · linarith only [h190, h201, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h203 | h203
                      · rcases h2bigk with h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c | h204c
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h0, hlam, p204_1]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          rcases p204_3 (m.d 0 2) (by simp) with h207 | h207
                          · rcases p204_3 (m.d 1 2) (by simp) with h208 | h208
                            · rcases p204_3 (m.d 2 3) (by simp) with h209 | h209
                              · linarith only [h209, hlam, p204_0]
                              · rcases p204_3 (m.d 2 4) (by simp) with h211 | h211
                                · linarith only [h190, h211, hlam]
                                · linarith only [h195, h211, hlam]
                            · linarith only [h192, h208, hlam]
                          · linarith only [h207, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht45, ht5b, p204_1, u0elo1, u4ehi2]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h201, hlam, hphi, ht0b, ht45, ht5b, p204_1, u0elo1, u4ehi2]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p204_1, u0ehi6]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          rcases p204_3 (m.d 0 2) (by simp) with h220 | h220
                          · linarith only [h0, h220, hlam]
                          · linarith only [h189, h220, hlam]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          rcases p204_3 (m.d 0 2) (by simp) with h223 | h223
                          · linarith only [h0, h223, hlam]
                          · linarith only [h190, h223, hlam]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          rcases p204_3 (m.d 0 2) (by simp) with h226 | h226
                          · linarith only [h0, h226, hlam]
                          · linarith only [h191, h226, hlam]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h189, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h192, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h195, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h197, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h190, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h193, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h191, h201, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p204_1, u0elo1]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h201, hlam, p204_1]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h191, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h194, hlam, p204_0]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h191, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p204_1, u0elo1]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [h191, hlam, hphi, ht0b, ht45, ht5b, p204_1, u0elo1, u4ehi2]
                        · have p204_0 := h204c.1
                          have p204_1 := h204c.2.1
                          have p204_2 := h204c.2.2.1
                          have p204_3 := h204c.2.2.2
                          linarith only [hlam, p204_0]
                      · rcases h2bigk with h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c | h244c
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h0, hlam, p244_1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          rcases p244_3 (m.d 0 2) (by simp) with h247 | h247
                          · rcases p244_3 (m.d 1 2) (by simp) with h248 | h248
                            · rcases p244_3 (m.d 2 3) (by simp) with h249 | h249
                              · linarith only [h249, hlam, p244_0]
                              · rcases p244_3 (m.d 2 4) (by simp) with h251 | h251
                                · linarith only [h190, h251, hlam]
                                · linarith only [h195, h251, hlam]
                            · linarith only [h192, h248, hlam]
                          · linarith only [h247, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, hphi, ht0b, ht45, ht5b, p244_1, u0elo1, u4ehi2]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h201, hlam, hphi, ht0b, ht45, ht5b, p244_1, u0elo1, u4ehi2]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hc12, hlam, hphi, ht01, p244_1, u0ehi6]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          rcases p244_3 (m.d 0 2) (by simp) with h260 | h260
                          · linarith only [h0, h260, hlam]
                          · linarith only [h189, h260, hlam]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          rcases p244_3 (m.d 0 2) (by simp) with h263 | h263
                          · linarith only [h0, h263, hlam]
                          · linarith only [h190, h263, hlam]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          rcases p244_3 (m.d 0 2) (by simp) with h266 | h266
                          · linarith only [h0, h266, hlam]
                          · linarith only [h191, h266, hlam]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h189, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h192, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h195, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h197, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h190, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h193, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h191, h201, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1, u0elo1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h201, hlam, p244_1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h191, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h194, hlam, p244_0]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h191, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p244_1, u0elo1]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [h191, hlam, hphi, ht0b, ht45, ht5b, p244_1, u0elo1, u4ehi2]
                        · have p244_0 := h244c.1
                          have p244_1 := h244c.2.1
                          have p244_2 := h244c.2.2.1
                          have p244_3 := h244c.2.2.2
                          linarith only [hlam, p244_0]
              · linarith only [h0, h191, h194, hlam, hphi, u0ehi5, u0elo1]
            · linarith only [h0, h193, hc24, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h0, h192, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
          · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
            · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
              · linarith only [h190, h191, h289, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · linarith only [h0, h289, hc25, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h190, h288, hlam, hphi, u0ehi5, u0elo1]
          · linarith only [h0, h287, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h294 | h294
        · rcases m.htr 1 2 3 (by decide) (by decide) with h295 | h295
          · rcases m.htr 1 2 4 (by decide) (by decide) with h296 | h296
            · linarith only [h190, h296, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h296, hc24, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h0, h189, h295, hlam, hphi, u0ehi5, u0elo1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
          · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
            · linarith only [h190, h301, hc12, hlam, hphi, ht01, u0ehi6]
            · linarith only [h0, h301, hc24, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h0, h189, h300, hlam, hphi, u0ehi5, u0elo1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h305 | h305
      · rcases m.htr 0 2 5 (by decide) (by decide) with h306 | h306
        · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
          · linarith only [h189, h305, h307, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · linarith only [h0, h307, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h310 | h310
          · linarith only [h189, h305, h310, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · linarith only [h0, h310, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h313 | h313
        · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
          · linarith only [h189, h314, hc12, hlam, hphi, ht01, u0ehi6]
          · linarith only [h0, h314, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
          · linarith only [h0, h189, h317, hc12, hlam, hphi, ht01, u0ehi5]
          · linarith only [h0, h317, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_21_15_M_IR_L_0 (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h5elo := hb5.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h4, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                        · rcases h1bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h11, h4, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h11, h6, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h11, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            rcases p13_3 (m.d 0 1) (by simp) with h18 | h18
                            · rcases p13_3 (m.d 1 2) (by simp) with h19 | h19
                              · linarith only [h0, h19, hlam]
                              · linarith only [h11, h19, h3, h4, h6, h8, hc34, hlam, hphi, ht45, u5elo0]
                            · linarith only [h18, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h0, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h11, h6, h8, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h0, h11, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h1, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h4, hlam, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h11, h8, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p13_1, u1ehi4]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h2, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h5, hlam, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h6, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hc14, hlam, hphi, p13_1, u1ehi4]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h3, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h10, h4, hc15, hc35, hlam, hphi, ht01, ht0b, ht5b, p13_1]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h7, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [h8, hlam, p13_0]
                          · have p13_0 := h13c.1
                            have p13_1 := h13c.2.1
                            have p13_2 := h13c.2.2.1
                            have p13_3 := h13c.2.2.2
                            linarith only [hlam, p13_0]
                      · linarith only [h10, h9, hc34, hlam, hphi, ht45, u5elo3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
                      · linarith only [h0, h4, h44, h6, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                        · rcases h1bigk with h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h4, h44, h46, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p47_1]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h44, h46, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p47_1]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            rcases p47_3 (m.d 0 1) (by simp) with h51 | h51
                            · rcases p47_3 (m.d 1 2) (by simp) with h52 | h52
                              · linarith only [h0, h52, hlam]
                              · linarith only [h5, h52, hlam]
                            · linarith only [h51, hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            rcases p47_3 (m.d 0 1) (by simp) with h56 | h56
                            · rcases p47_3 (m.d 1 2) (by simp) with h57 | h57
                              · linarith only [h0, h57, hlam]
                              · linarith only [h4, h44, h46, h57, h6, hc23, hlam, hphi, ht34, ht45, u5elo1]
                            · linarith only [h56, hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h0, hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h44, h46, h6, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p47_1]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p47_1, u1ehi3]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p47_1, u1ehi4]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h1, hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h4, hlam, p47_1]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h8, hc13, hlam, hphi, p47_1, u1ehi4]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p47_1, u1ehi4]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h2, hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h5, hlam, p47_1]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h6, hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [hc14, hlam, hphi, p47_1, u1ehi4]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h3, hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [hc15, hlam, hphi, p47_1, u1ehi1]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h7, hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [h8, hlam, p47_0]
                          · have p47_0 := h47c.1
                            have p47_1 := h47c.2.1
                            have p47_2 := h47c.2.2.1
                            have p47_3 := h47c.2.2.2
                            linarith only [hlam, p47_0]
                        · linarith only [h0, h4, h46, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h8, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                · linarith only [h7, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
                · rcases m.htr 1 4 5 (by decide) (by decide) with h85 | h85
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h86 | h86
                    · linarith only [h6, h84, h86, hc23, hlam, hphi, ht12, u1ehi4]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h88 | h88
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                        · rcases h1bigk with h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c | h90c
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h4, h88, hc01, hc35, hlam, hphi, ht0b, ht5b, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            rcases p90_3 (m.d 0 1) (by simp) with h93 | h93
                            · rcases p90_3 (m.d 1 2) (by simp) with h94 | h94
                              · linarith only [h0, h94, hlam]
                              · linarith only [h4, h94, hlam]
                            · linarith only [h93, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            rcases p90_3 (m.d 0 1) (by simp) with h98 | h98
                            · rcases p90_3 (m.d 1 2) (by simp) with h99 | h99
                              · linarith only [h0, h99, hlam]
                              · linarith only [h5, h99, hlam]
                            · linarith only [h98, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            rcases p90_3 (m.d 0 1) (by simp) with h103 | h103
                            · rcases p90_3 (m.d 1 2) (by simp) with h104 | h104
                              · linarith only [h0, h104, hlam]
                              · linarith only [h104, h5, h86, h88, h89, hc45, hlam, hphi, u5elo1]
                            · linarith only [h103, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hc12, hlam, hphi, p90_1, u1ehi2]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p90_1, u1ehi2]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p90_1, u1ehi4]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h1, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h4, hlam, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h6, hlam, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hc13, hlam, hphi, p90_1, u1ehi4]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h2, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h5, hlam, p90_1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hc14, hlam, hphi, p90_1, u1ehi2]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p90_1, u1ehi4]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h3, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h84, hc13, hlam, hphi, p90_1, u1ehi1]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h84, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [h85, hlam, p90_0]
                          · have p90_0 := h90c.1
                            have p90_1 := h90c.2.1
                            have p90_2 := h90c.2.2.1
                            have p90_3 := h90c.2.2.2
                            linarith only [hlam, p90_0]
                        · linarith only [h6, h89, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                      · linarith only [h6, h84, h88, hc23, hc34, hlam, hphi]
                  · linarith only [h6, h84, h85, hc35, hlam, hphi, u5elo4]
                · linarith only [h84, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
              · linarith only [h132, h4, h5, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                    · linarith only [h132, h136, hc23, hlam, hphi, ht12, u1ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h138 | h138
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h139 | h139
                        · rcases h1bigk with h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c | h140c
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h138, h139, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            rcases p140_3 (m.d 0 1) (by simp) with h143 | h143
                            · rcases p140_3 (m.d 1 2) (by simp) with h144 | h144
                              · linarith only [h0, h144, hlam]
                              · linarith only [h144, h4, hlam]
                            · linarith only [h143, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h138, h139, h4, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            rcases p140_3 (m.d 0 1) (by simp) with h149 | h149
                            · rcases p140_3 (m.d 1 2) (by simp) with h150 | h150
                              · linarith only [h0, h150, hlam]
                              · linarith only [h138, h139, h150, h4, hc45, hlam, hphi, u5elo1]
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
                            linarith only [h136, h5, hc13, hc34, hlam, hphi, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h5, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h136, h5, hc34, hlam, hphi, ht12, ht23, p140_1, u1ehi4]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h1, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h4, hlam, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h132, hlam, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hc13, hlam, hphi, p140_1, u1ehi4]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h2, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h138, h139, h4, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h136, h138, h139, h2, h4, h5, hc01, hc34, hc45, hlam, hphi, ht0b, ht12, ht23, ht5b, p140_1, u1ehi2]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h136, h138, h139, h2, h4, h5, hc01, hc34, hc45, hlam, hphi, ht0b, ht12, ht23, ht5b, p140_1, u1ehi4]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h3, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h134, h138, h139, h4, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p140_1]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h134, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [h135, hlam, p140_0]
                          · have p140_0 := h140c.1
                            have p140_1 := h140c.2.1
                            have p140_2 := h140c.2.2.1
                            have p140_3 := h140c.2.2.2
                            linarith only [hlam, p140_0]
                        · linarith only [h136, h139, h4, h5, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h134, h136, h138, h4, h5, hc23, hc34, hlam, hphi]
                  · linarith only [h135, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                · linarith only [h134, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
            · rcases m.htr 1 3 4 (by decide) (by decide) with h179 | h179
              · rcases m.htr 1 3 5 (by decide) (by decide) with h180 | h180
                · rcases m.htr 1 4 5 (by decide) (by decide) with h181 | h181
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h182 | h182
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h184 | h184
                        · rcases h1bigk with h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h178, h182, h184, hc01, hc45, hlam, hphi, ht0b, ht5b, p185_1]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h178, h182, h184, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p185_1]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            rcases p185_3 (m.d 0 1) (by simp) with h189 | h189
                            · rcases p185_3 (m.d 1 2) (by simp) with h190 | h190
                              · linarith only [h0, h190, hlam]
                              · linarith only [h178, h190, hlam]
                            · linarith only [h189, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            rcases p185_3 (m.d 0 1) (by simp) with h194 | h194
                            · rcases p185_3 (m.d 1 2) (by simp) with h195 | h195
                              · linarith only [h0, h195, hlam]
                              · linarith only [h178, h182, h184, h195, hc45, hlam, hphi, u5elo1]
                            · linarith only [h194, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h0, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h4, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [hc12, hlam, hphi, p185_1, u1ehi3]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht12, p185_1, u1ehi4]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h1, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p185_1, u1ehi1]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h1, h181, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p185_1, u1ehi4]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p185_1, u1ehi4]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h2, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h178, hlam, p185_1]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h179, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [hc14, hlam, hphi, p185_1, u1ehi4]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h3, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [hc15, hlam, hphi, p185_1, u1ehi1]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h180, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [h181, hlam, p185_0]
                          · have p185_0 := h185c.1
                            have p185_1 := h185c.2.1
                            have p185_2 := h185c.2.2.1
                            have p185_3 := h185c.2.2.2
                            linarith only [hlam, p185_0]
                        · rcases h1bigk with h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c | h219c
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h178, h181, h184, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p219_1]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h178, h181, h184, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p219_1]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h181, h184, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p219_1]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            rcases p219_3 (m.d 0 1) (by simp) with h224 | h224
                            · rcases p219_3 (m.d 1 2) (by simp) with h225 | h225
                              · linarith only [h0, h225, hlam]
                              · linarith only [h178, h181, h184, h225, h3, hc34, hlam, hphi, ht45, u5elo0]
                            · linarith only [h224, hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h0, hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h4, hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h181, h184, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p219_1]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht12, p219_1, u1ehi4]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h1, hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h1, h178, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p219_1]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h1, h181, h184, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p219_1]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p219_1, u1ehi4]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h2, hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h178, hlam, p219_1]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h179, hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h178, hc12, hlam, hphi, p219_1, u1ehi4]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h3, hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [hc15, hlam, hphi, p219_1, u1ehi1]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h180, hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [h181, hlam, p219_0]
                          · have p219_0 := h219c.1
                            have p219_1 := h219c.2.1
                            have p219_2 := h219c.2.2.1
                            have p219_3 := h219c.2.2.2
                            linarith only [hlam, p219_0]
                      · linarith only [h178, h181, h183, h4, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi4, u5elo3]
                    · linarith only [h178, h181, h182, h4, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                  · linarith only [h181, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                · linarith only [h180, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi2, u5elo3]
              · linarith only [h178, h179, h4, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h254 | h254
              · rcases m.htr 1 3 5 (by decide) (by decide) with h255 | h255
                · rcases m.htr 1 4 5 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h258 | h258
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                        · rcases h1bigk with h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            rcases p260_3 (m.d 0 1) (by simp) with h262 | h262
                            · rcases p260_3 (m.d 1 2) (by simp) with h263 | h263
                              · linarith only [h263, hlam, p260_0]
                              · rcases p260_3 (m.d 1 3) (by simp) with h265 | h265
                                · linarith only [h1, h265, hlam]
                                · linarith only [h265, h4, hlam]
                            · linarith only [h262, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h254, h259, hc01, hc45, hlam, hphi, ht0b, ht5b, p260_1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            rcases p260_3 (m.d 0 1) (by simp) with h270 | h270
                            · rcases p260_3 (m.d 1 2) (by simp) with h271 | h271
                              · linarith only [h0, h271, hlam]
                              · rcases p260_3 (m.d 1 3) (by simp) with h273 | h273
                                · linarith only [h1, h273, hlam]
                                · linarith only [h254, h273, hlam]
                            · linarith only [h270, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            rcases p260_3 (m.d 0 1) (by simp) with h277 | h277
                            · rcases p260_3 (m.d 1 2) (by simp) with h278 | h278
                              · linarith only [h0, h278, hlam]
                              · rcases p260_3 (m.d 1 3) (by simp) with h280 | h280
                                · linarith only [h1, h280, hlam]
                                · linarith only [h255, h280, hlam]
                            · linarith only [h277, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h0, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h4, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h178, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hc12, hlam, hphi, p260_1, u1ehi4]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h1, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hc13, hlam, hphi, p260_1, u1ehi1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h1, h178, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p260_1, u1ehi1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hc13, hlam, hphi, p260_1, u1ehi4]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h2, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hc14, hlam, hphi, p260_1, u1ehi1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h254, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h1, h254, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p260_1, u1ehi4]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h3, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hc15, hlam, hphi, p260_1, u1ehi1]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h255, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [h256, hlam, p260_0]
                          · have p260_0 := h260c.1
                            have p260_1 := h260c.2.1
                            have p260_2 := h260c.2.2.1
                            have p260_3 := h260c.2.2.2
                            linarith only [hlam, p260_0]
                        · rcases h1bigk with h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c | h304c
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            rcases p304_3 (m.d 0 1) (by simp) with h306 | h306
                            · rcases p304_3 (m.d 1 2) (by simp) with h307 | h307
                              · linarith only [h307, hlam, p304_0]
                              · rcases p304_3 (m.d 1 3) (by simp) with h309 | h309
                                · linarith only [h1, h309, hlam]
                                · linarith only [h309, h4, hlam]
                            · linarith only [h306, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h254, h256, h259, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p304_1]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h256, h259, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p304_1]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            rcases p304_3 (m.d 0 1) (by simp) with h315 | h315
                            · rcases p304_3 (m.d 1 2) (by simp) with h316 | h316
                              · linarith only [h0, h316, hlam]
                              · rcases p304_3 (m.d 1 3) (by simp) with h318 | h318
                                · linarith only [h1, h318, hlam]
                                · linarith only [h255, h318, hlam]
                            · linarith only [h315, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h0, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h4, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h178, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [hc12, hlam, hphi, p304_1, u1ehi4]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h1, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [hc13, hlam, hphi, p304_1, u1ehi1]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h1, h256, h259, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p304_1]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p304_1, u1ehi4]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h2, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [hc14, hlam, hphi, p304_1, u1ehi1]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h254, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h1, h254, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p304_1, u1ehi4]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h3, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [hc15, hlam, hphi, p304_1, u1ehi1]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h255, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [h256, hlam, p304_0]
                          · have p304_0 := h304c.1
                            have p304_1 := h304c.2.1
                            have p304_2 := h304c.2.2.1
                            have p304_3 := h304c.2.2.2
                            linarith only [hlam, p304_0]
                      · linarith only [h258, h4, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo3]
                    · linarith only [h257, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h256, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi3, u5elo4]
                · linarith only [h254, h255, hc34, hlam, hphi, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h346 | h346
                · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h348 | h348
                    · linarith only [h254, h348, h4, hc23, hlam, hphi, ht12, u1ehi1]
                    · linarith only [h348, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h254, h347, h4, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo4]
                · linarith only [h346, h4, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi1, u5elo3]
        · linarith only [h3, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h356 | h356
    · linarith only [h0, h356, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h358 | h358
      · linarith only [h0, h358, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h360 | h360
        · linarith only [h0, h360, hc12, hlam, hphi, u1ehi4]
        · linarith only [h360, hlam, hphi, ht12, ht23, ht34, ht45, u1ehi0, u5elo1]

end R2N4
