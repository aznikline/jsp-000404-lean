import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_M_LR_L_I_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · linarith only [h0, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · linarith only [h1, h4, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
              · linarith only [h0, h1, h4, h8, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h1, h10, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12 | h12
                  · linarith only [h0, h10, h12, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h0, h14, h2, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                      · linarith only [h10, h14, h16, h4, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h10, h16, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h19 | h19
          · linarith only [h0, h19, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · linarith only [h1, h19, h3, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
        · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
          · linarith only [h0, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · linarith only [h1, h2, h23, hc12, hc24, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
          · linarith only [h0, h26, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
          · linarith only [h1, h2, h26, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h29 | h29
      · rcases m.htr 0 2 5 (by decide) (by decide) with h30 | h30
        · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
          · linarith only [h1, h30, h31, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
            · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
              · linarith only [h0, h34, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · linarith only [h1, h30, h34, hc12, hc23, hlam, hphi]
            · linarith only [h1, h29, h33, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
          · linarith only [h1, h38, hc12, hlam, hphi, ht01, u0ehi6]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h40 | h40
            · rcases m.htr 1 2 5 (by decide) (by decide) with h41 | h41
              · linarith only [h0, h29, h30, h41, hlam, hphi, u0ehi8, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                · linarith only [h0, h40, h43, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                · linarith only [h1, h29, h43, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
            · linarith only [h1, h29, h40, hc12, hc23, hlam, hphi]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h47 | h47
        · rcases m.htr 1 2 3 (by decide) (by decide) with h48 | h48
          · linarith only [h1, h47, h48, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h50 | h50
            · linarith only [h0, h29, h47, h50, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h52 | h52
              · linarith only [h0, h52, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi2]
              · linarith only [h1, h47, h52, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
          · linarith only [h1, h55, hc12, hlam, hphi, ht01, u0ehi6]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
            · linarith only [h0, h29, h57, hlam, hphi, u0ehi6, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h59 | h59
              · linarith only [h0, h47, h59, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h61 | h61
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
                          linarith only [h47, h61, h63, hc12, hc23, hlam, hphi, p65_1]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h1, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h29, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h47, hlam, p65_0]
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
                          linarith only [h55, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h57, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h59, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p65_1, u0ehi6]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          rcases p65_3 (m.d 0 2) (by simp) with h77 | h77
                          · linarith only [h1, h77, hlam]
                          · linarith only [h0, h77, hlam]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h29, hc23, hlam, hphi, ht01, ht12, p65_1, u0ehi6]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h47, hc23, hlam, hphi, ht01, ht12, p65_1, u0ehi6]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hc24, hlam, hphi, ht01, ht12, p65_1, u0ehi6]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          rcases p65_3 (m.d 0 2) (by simp) with h84 | h84
                          · linarith only [h29, h84, hlam]
                          · linarith only [h0, h84, hlam]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h61, hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hlam, p65_0]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [h47, h61, hc23, hlam, hphi, ht01, ht12, p65_1, u0ehi6]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht12, p65_1, u0ehi6]
                        · have p65_0 := h65c.1
                          have p65_1 := h65c.2.1
                          have p65_2 := h65c.2.2.1
                          have p65_3 := h65c.2.2.2
                          rcases p65_3 (m.d 0 2) (by simp) with h91 | h91
                          · linarith only [h47, h91, hlam]
                          · linarith only [h0, h91, hlam]
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
                      · rcases h2bigk with h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h1, hc12, hc23, hlam, hphi, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h1, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h29, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h47, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, hlam, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h55, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h57, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h59, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p97_1, u0ehi6]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 2) (by simp) with h109 | h109
                          · linarith only [h1, h109, hlam]
                          · linarith only [h0, h109, hlam]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h63, h64, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p97_1, u3ehi3]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h47, hc23, hlam, hphi, ht01, ht12, p97_1, u0ehi6]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hc24, hlam, hphi, ht01, ht12, p97_1, u0ehi6]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 2) (by simp) with h116 | h116
                          · linarith only [h116, h29, hlam]
                          · linarith only [h0, h116, hlam]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h61, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h47, h61, hc23, hlam, hphi, ht01, ht12, p97_1, u0ehi6]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht12, p97_1, u0ehi6]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 2) (by simp) with h123 | h123
                          · linarith only [h123, h47, hlam]
                          · linarith only [h0, h123, hlam]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h62, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h63, hlam, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                    · linarith only [h29, h63, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                  · linarith only [h1, h62, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h1, h61, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h132 | h132
    · rcases m.htr 0 2 4 (by decide) (by decide) with h133 | h133
      · rcases m.htr 0 2 5 (by decide) (by decide) with h134 | h134
        · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
          · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
            · rcases m.htr 1 2 5 (by decide) (by decide) with h137 | h137
              · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                · linarith only [h132, h138, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h140 | h140
                  · linarith only [h133, h138, h140, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi3]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h142 | h142
                    · linarith only [h133, h142, hlam, hphi, ht0b, ht5b, u0elo1, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h144 | h144
                      · linarith only [h138, h142, h144, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h138, h144, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h134, h137, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h136, hc24, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h0, h135, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
          · rcases m.htr 1 2 4 (by decide) (by decide) with h151 | h151
            · rcases m.htr 1 2 5 (by decide) (by decide) with h152 | h152
              · linarith only [h132, h134, h152, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h152, hc25, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h0, h133, h151, hlam, hphi, u0ehi5, u0elo1]
          · linarith only [h0, h150, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h157 | h157
        · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
          · rcases m.htr 1 2 4 (by decide) (by decide) with h159 | h159
            · linarith only [h132, h133, h159, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h159, hc24, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h0, h132, h158, hlam, hphi, u0ehi5, u0elo1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
          · rcases m.htr 1 2 4 (by decide) (by decide) with h164 | h164
            · linarith only [h132, h133, h164, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · linarith only [h0, h164, hc24, hlam, hphi, ht01, ht12, u0ehi5]
          · linarith only [h0, h132, h163, hlam, hphi, u0ehi5, u0elo1]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h168 | h168
      · rcases m.htr 0 2 5 (by decide) (by decide) with h169 | h169
        · rcases m.htr 1 2 3 (by decide) (by decide) with h170 | h170
          · linarith only [h132, h169, h170, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · linarith only [h0, h170, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h173 | h173
          · linarith only [h132, h173, hc12, hlam, hphi, ht01, u0ehi6]
          · linarith only [h0, h173, hc23, hlam, hphi, ht01, ht12, u0ehi5]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h176 | h176
        · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
          · linarith only [h0, h132, h177, hc12, hlam, hphi, ht01, u0ehi5]
          · linarith only [h0, h177, hc23, hlam, hphi, ht01, ht12, u0ehi5]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h180 | h180
          · linarith only [h0, h132, h180, hc12, hlam, hphi, ht01, u0ehi5]
          · linarith only [h0, h180, hc23, hlam, hphi, ht01, ht12, u0ehi5]

theorem r1l7_20_12_13_H_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have hc14 := m.hcor 1 4 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h3elo := hb3.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases h0bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi3]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h1, h10, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, h2, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi3]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h1, hlam, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h3, hlam, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h2, h9, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi3]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h5, hlam, hphi, ht23, p11_1, u2ehi4, u3elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h2, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h4, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h6, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h5, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi4]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h0, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h5, hlam, p11_1]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h7, hlam, p11_0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [h7, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p11_1, u3elo0]
                        · have p11_0 := h11c.1
                          have p11_1 := h11c.2.1
                          have p11_2 := h11c.2.2.1
                          have p11_3 := h11c.2.2.2
                          linarith only [hlam, p11_0]
                      · linarith only [h10, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h4, h6, h9, hlam, hphi, ht23, u2ehi1, u3elo0]
                  · linarith only [h8, hlam, hphi, ht23, u2ehi1, u3elo2]
                · linarith only [h3, h7, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h3, h6, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · linarith only [h3, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h45 | h45
        · rcases m.htr 0 2 4 (by decide) (by decide) with h46 | h46
          · linarith only [h0, h2, h46, hlam]
          · linarith only [h45, h46, hc24, hlam, hphi, u2ehi2]
        · linarith only [h45, hlam, hphi, ht23, u2ehi0, u3elo2]
    · linarith only [h0, h1, hlam, hphi, ht23, u2ehi1, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h51 | h51
    · rcases m.htr 0 1 4 (by decide) (by decide) with h52 | h52
      · rcases m.htr 0 2 3 (by decide) (by decide) with h53 | h53
        · rcases m.htr 0 2 4 (by decide) (by decide) with h54 | h54
          · rcases m.htr 0 2 5 (by decide) (by decide) with h55 | h55
            · rcases m.htr 0 3 4 (by decide) (by decide) with h56 | h56
              · rcases m.htr 0 3 5 (by decide) (by decide) with h57 | h57
                · rcases m.htr 1 2 3 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                      · rcases h0bigk with h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c | h61c
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [hlam, p61_0]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h0, hlam, p61_1]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h52, h56, h59, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h0, h52, h59, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p61_1]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p61_1]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [hlam, p61_0]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h0, h52, h56, h59, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h0, h52, h59, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h0, h55, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi4]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h51, hlam, p61_1]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h53, hlam, p61_1]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [hlam, p61_0]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h52, h59, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h55, hlam, hphi, ht23, p61_1, u2ehi4, u3elo0]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h52, hlam, p61_0]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h54, hlam, p61_0]
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
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h55, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi4]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h51, h58, h60, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p61_1, u2ehi3]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h55, hlam, p61_1]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h57, hlam, p61_0]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [h57, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p61_1, u3elo0]
                        · have p61_0 := h61c.1
                          have p61_1 := h61c.2.1
                          have p61_2 := h61c.2.2.1
                          have p61_3 := h61c.2.2.2
                          linarith only [hlam, p61_0]
                      · linarith only [h60, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h0, h51, h58, h59, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h58, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h53, h57, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h53, h56, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h53, h55, hc25, hlam, hphi, u2ehi2]
          · linarith only [h53, h54, hc24, hlam, hphi, u2ehi2]
        · linarith only [h53, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h95 | h95
        · rcases m.htr 0 2 4 (by decide) (by decide) with h96 | h96
          · rcases m.htr 0 2 5 (by decide) (by decide) with h97 | h97
            · rcases m.htr 0 3 4 (by decide) (by decide) with h98 | h98
              · linarith only [h51, h52, h98, hlam]
              · linarith only [h95, h98, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h95, h97, hc25, hlam, hphi, u2ehi2]
          · linarith only [h95, h96, hc24, hlam, hphi, u2ehi2]
        · linarith only [h95, hlam, hphi, ht23, u2ehi0, u3elo2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h104 | h104
      · rcases m.htr 0 2 3 (by decide) (by decide) with h105 | h105
        · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
          · linarith only [h104, h106, h51, hlam, hphi, ht23, u2ehi3, u3elo1]
          · linarith only [h105, h106, hc24, hlam, hphi, u2ehi2]
        · linarith only [h105, hlam, hphi, ht23, u2ehi0, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h110 | h110
        · rcases m.htr 0 2 4 (by decide) (by decide) with h111 | h111
          · rcases m.htr 0 2 5 (by decide) (by decide) with h112 | h112
            · rcases m.htr 0 3 4 (by decide) (by decide) with h113 | h113
              · rcases m.htr 0 3 5 (by decide) (by decide) with h114 | h114
                · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                      · rcases h0bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [hlam, p118_0]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h0, hlam, p118_1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h51, hlam, p118_0]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h104, hlam, p118_1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h51, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p118_1, u3elo1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p118_1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [hlam, p118_0]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h0, h111, h113, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p118_1, u2ehi3]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h0, h111, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p118_1, u2ehi3]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h0, h112, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p118_1, u2ehi4]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [hc01, hlam, hphi, ht12, ht23, p118_1, u3elo0]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h110, hlam, p118_1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [hlam, p118_0]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h111, h51, hlam, hphi, ht23, p118_1, u2ehi3, u3elo1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h112, h51, hlam, hphi, ht23, p118_1, u2ehi4, u3elo1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h104, hc01, hc14, hlam, hphi, p118_1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h111, hlam, p118_0]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h113, hlam, p118_0]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [hlam, p118_0]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h112, h113, h51, hlam, hphi, ht23, p118_1, u2ehi4, u3elo1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h0, h112, hc01, hc12, hlam, hphi, p118_1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h112, hlam, p118_1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h114, hlam, p118_0]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [h114, h51, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p118_1, u3elo1]
                        · have p118_0 := h118c.1
                          have p118_1 := h118c.2.1
                          have p118_2 := h118c.2.2.1
                          have p118_3 := h118c.2.2.2
                          linarith only [hlam, p118_0]
                      · linarith only [h117, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · linarith only [h0, h110, h116, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h110, h115, hlam]
                · linarith only [h110, h114, hlam, hphi, ht23, u2ehi2, u3elo4]
              · linarith only [h110, h113, hlam, hphi, ht23, u2ehi2, u3elo3]
            · linarith only [h110, h112, hc25, hlam, hphi, u2ehi2]
          · linarith only [h110, h111, hc24, hlam, hphi, u2ehi2]
        · linarith only [h110, hlam, hphi, ht23, u2ehi0, u3elo2]

theorem r1l7_20_12_13_M_LR_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h0elo := hb0.1
  have h0ehi := hb0.2.2.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h2, h5, h8, h9, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14 | h14
                    · linarith only [h14, h2, h4, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                      · linarith only [h16, h2, h8, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h18 | h18
                        · linarith only [h14, h18, h6, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h20 | h20
                          · rcases h3bigk with h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              rcases p21_3 (m.d 0 3) (by simp) with h23 | h23
                              · rcases p21_3 (m.d 1 3) (by simp) with h24 | h24
                                · linarith only [h1, h24, hlam]
                                · rcases p21_3 (m.d 2 3) (by simp) with h26 | h26
                                  · linarith only [h2, h26, hlam]
                                  · rcases p21_3 (m.d 3 4) (by simp) with h28 | h28
                                    · linarith only [h28, h4, hlam]
                                    · linarith only [h28, h8, hlam]
                              · linarith only [h1, h23, hlam]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              rcases p21_3 (m.d 0 3) (by simp) with h32 | h32
                              · rcases p21_3 (m.d 1 3) (by simp) with h33 | h33
                                · linarith only [h1, h33, hlam]
                                · linarith only [h33, h6, hlam]
                              · linarith only [h2, h32, hlam]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, h2, h20, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, h2, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h1, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, h20, hc23, hc34, hlam, hphi, p21_1]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h8, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h2, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h6, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h16, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h18, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h4, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h2, h4, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h14, h2, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h5, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h2, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p21_1, u2elo0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [h20, hlam, p21_0]
                            · have p21_0 := h21c.1
                              have p21_1 := h21c.2.1
                              have p21_2 := h21c.2.2.1
                              have p21_3 := h21c.2.2.2
                              linarith only [hlam, p21_0]
                          · rcases h3bigk with h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c | h59c
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              rcases p59_3 (m.d 0 3) (by simp) with h61 | h61
                              · rcases p59_3 (m.d 1 3) (by simp) with h62 | h62
                                · linarith only [h1, h62, hlam]
                                · rcases p59_3 (m.d 2 3) (by simp) with h64 | h64
                                  · linarith only [h2, h64, hlam]
                                  · rcases p59_3 (m.d 3 4) (by simp) with h66 | h66
                                    · linarith only [h4, h66, hlam]
                                    · linarith only [h66, h8, hlam]
                              · linarith only [h1, h61, hlam]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              rcases p59_3 (m.d 0 3) (by simp) with h70 | h70
                              · rcases p59_3 (m.d 1 3) (by simp) with h71 | h71
                                · linarith only [h1, h71, hlam]
                                · linarith only [h6, h71, hlam]
                              · linarith only [h2, h70, hlam]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h2, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h14, h2, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h1, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h8, hc23, hc34, hlam, hphi, p59_1]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h8, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h14, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h2, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h6, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h16, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h18, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h4, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h20, hc13, hc45, hlam, hphi, ht34, p59_1]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h20, hlam, p59_1]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h5, hlam, p59_0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h2, h5, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p59_1, u2elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [h16, h2, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p59_1, u2elo0]
                            · have p59_0 := h59c.1
                              have p59_1 := h59c.2.1
                              have p59_2 := h59c.2.2.1
                              have p59_3 := h59c.2.2.2
                              linarith only [hlam, p59_0]
                · linarith only [h3, h7, hc12, hlam, hphi, u2elo0]
              · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h99 | h99
              · rcases m.htr 1 2 5 (by decide) (by decide) with h100 | h100
                · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                    · linarith only [h102, h5, hc13, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                      · linarith only [h0, h104, h99, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h101, h104, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h101, h4, h5, hc13, hc35, hlam, hphi]
                · linarith only [h100, h3, hc12, hlam, hphi, u2elo0]
              · linarith only [h2, h99, hc12, hlam, hphi, u2elo0]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
            · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
              · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
                · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                  · linarith only [h113, h4, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                      · linarith only [h110, h111, h116, h4, hc12, hlam, hphi, ht01, u0ehi9]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                        · linarith only [h0, h111, h118, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h110, h118, h4, hc23, hc34, hlam, hphi]
                    · linarith only [h110, h115, h4, hc13, hc34, hlam, hphi]
                · linarith only [h112, h3, hc12, hlam, hphi, u2elo0]
              · linarith only [h111, h2, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h124 | h124
              · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                  · linarith only [h126, h4, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                    · linarith only [h110, h124, h128, hc12, hlam, hphi, ht01, u0ehi7]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                      · linarith only [h130, h4, hlam, hphi, ht01, ht12, u0ehi7, u2elo2]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                        · linarith only [h0, h110, h124, h132, hlam, hphi, u0ehi7, u0elo0]
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
                              linarith only [h110, h134, hc13, hc34, hlam, hphi, p135_1]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h110, h134, hc23, hc34, hlam, hphi, p135_1]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h4, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h110, hlam, p135_0]
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
                              linarith only [h1, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p135_1, u0elo0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h126, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h128, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h2, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h124, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h130, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h132, hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p135_1, u0ehi7]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              rcases p135_3 (m.d 0 3) (by simp) with h152 | h152
                              · linarith only [h152, h4, hlam]
                              · linarith only [h1, h152, hlam]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              rcases p135_3 (m.d 0 3) (by simp) with h155 | h155
                              · linarith only [h155, h4, hlam]
                              · linarith only [h155, h2, hlam]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [hlam, p135_0]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [h110, hc34, hlam, hphi, ht01, ht12, ht23, p135_1, u0ehi7]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p135_1, u0ehi7]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              rcases p135_3 (m.d 0 3) (by simp) with h161 | h161
                              · linarith only [h110, h161, hlam]
                              · linarith only [h1, h161, hlam]
                            · have p135_0 := h135c.1
                              have p135_1 := h135c.2.1
                              have p135_2 := h135c.2.2.1
                              have p135_3 := h135c.2.2.2
                              rcases p135_3 (m.d 0 3) (by simp) with h164 | h164
                              · linarith only [h110, h164, hlam]
                              · linarith only [h164, h2, hlam]
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
                          · linarith only [h134, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                · linarith only [h125, h3, hc12, hlam, hphi, u2elo0]
              · linarith only [h124, h2, hc12, hlam, hphi, u2elo0]
        · linarith only [h3, hlam, hphi, ht01, ht12, u0ehi6, u2elo4]
      · linarith only [h2, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h174 | h174
      · linarith only [h0, h1, h174, hlam]
      · linarith only [h174, hlam, hphi, ht01, ht12, u0ehi6, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi5, u2elo1]

theorem r1l7_20_12_14_H_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0bigk := hb0.1
  have h2ehi := hb2.1
  have h4elo := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                          · linarith only [h0, h10, h12, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
                          · linarith only [h12, h7, hc34, hlam, hphi, u4elo0]
                        · linarith only [h11, h7, hc24, hlam, hphi, u4elo0]
                      · linarith only [h10, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                    · linarith only [h9, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h18 | h18
                    · linarith only [h18, h8, hc23, hlam, hphi, u2ehi3]
                    · linarith only [h18, hlam, hphi, ht23, ht34, u2ehi1, u4elo2]
                · linarith only [h4, h7, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
              · linarith only [h3, h6, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
            · linarith only [h3, h5, hc25, hlam, hphi, u2ehi2]
          · linarith only [h3, h4, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h25 | h25
          · linarith only [h25, h3, hc23, hlam, hphi, u2ehi3]
          · linarith only [h25, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
      · linarith only [h0, h2, hlam, hphi, ht23, ht34, u2ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
      · rcases m.htr 0 2 3 (by decide) (by decide) with h30 | h30
        · linarith only [h0, h1, h30, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h32 | h32
          · linarith only [h30, h32, hc23, hlam, hphi, u2ehi3]
          · linarith only [h32, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
      · linarith only [h0, h29, hlam, hphi, ht23, ht34, u2ehi1, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h36 | h36
    · rcases m.htr 0 1 4 (by decide) (by decide) with h37 | h37
      · rcases m.htr 0 2 3 (by decide) (by decide) with h38 | h38
        · rcases m.htr 0 2 4 (by decide) (by decide) with h39 | h39
          · rcases m.htr 0 2 5 (by decide) (by decide) with h40 | h40
            · rcases m.htr 0 3 4 (by decide) (by decide) with h41 | h41
              · rcases m.htr 0 4 5 (by decide) (by decide) with h42 | h42
                · rcases m.htr 1 2 3 (by decide) (by decide) with h43 | h43
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h44 | h44
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h45 | h45
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h46 | h46
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                          · linarith only [h0, h36, h43, h45, h47, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h42, h47, hc34, hlam, hphi, u4elo0]
                        · linarith only [h42, h46, hc24, hlam, hphi, u4elo0]
                      · linarith only [h45, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                    · linarith only [h0, h36, h43, h44, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h39, h43, hc23, hlam, hphi, u2ehi3]
                · linarith only [h39, h42, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
              · linarith only [h38, h41, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
            · linarith only [h39, h40, hc25, hlam, hphi, u2ehi3]
          · linarith only [h39, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
        · linarith only [h0, h36, h38, hlam]
      · linarith only [h36, h37, hc13, hlam, hphi, ht34, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h60 | h60
      · rcases m.htr 0 2 3 (by decide) (by decide) with h61 | h61
        · rcases m.htr 0 2 4 (by decide) (by decide) with h62 | h62
          · rcases m.htr 0 2 5 (by decide) (by decide) with h63 | h63
            · rcases m.htr 0 3 4 (by decide) (by decide) with h64 | h64
              · rcases m.htr 0 4 5 (by decide) (by decide) with h65 | h65
                · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h67 | h67
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h70 | h70
                          · rcases h0bigk with h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c | h71c
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [hlam, p71_0]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h0, hlam, p71_1]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h36, hlam, p71_0]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h36, h60, h66, h67, h69, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h36, h63, h66, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p71_1]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [hlam, p71_0]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h0, h36, h60, h67, h69, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h0, h60, h67, h69, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h0, h63, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h60, h67, h69, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h61, hlam, p71_1]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [hlam, p71_0]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h36, h60, h66, h67, h69, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h36, h63, h66, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h60, hlam, p71_0]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h62, hlam, p71_0]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h64, hlam, p71_0]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [hlam, p71_0]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h63, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h60, h67, h69, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p71_1, u2ehi4]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h63, hlam, p71_1]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h65, hc03, hlam, hphi, ht34, p71_1, u4elo0]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [h65, hlam, p71_1]
                            · have p71_0 := h71c.1
                              have p71_1 := h71c.2.1
                              have p71_2 := h71c.2.2.1
                              have p71_3 := h71c.2.2.2
                              linarith only [hlam, p71_0]
                          · linarith only [h65, h70, hc34, hlam, hphi, u4elo0]
                        · linarith only [h65, h69, hc24, hlam, hphi, u4elo0]
                      · linarith only [h68, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                    · linarith only [h0, h67, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
                  · linarith only [h0, h60, h62, h66, hc23, hlam, hphi, u2ehi3]
                · linarith only [h62, h65, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
              · linarith only [h36, h60, h62, h64, hlam, hphi, ht23, ht34, u2ehi3, u4elo3]
            · linarith only [h61, h63, hc25, hlam, hphi, u2ehi2]
          · linarith only [h61, h62, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h106 | h106
          · linarith only [h106, h61, hc23, hlam, hphi, u2ehi3]
          · linarith only [h106, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h109 | h109
        · rcases m.htr 0 2 4 (by decide) (by decide) with h110 | h110
          · rcases m.htr 0 2 5 (by decide) (by decide) with h111 | h111
            · rcases m.htr 0 3 4 (by decide) (by decide) with h112 | h112
              · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
                · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h116 | h116
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h117 | h117
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h118 | h118
                          · rcases h0bigk with h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c | h119c
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [hlam, p119_0]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h0, hlam, p119_1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h36, hlam, p119_0]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h60, hlam, p119_1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h111, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p119_1, u2ehi4]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p119_1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [hlam, p119_0]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h0, h109, h116, h118, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p119_1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h0, h111, h113, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p119_1, u2ehi4]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h0, h111, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p119_1, u2ehi4]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h36, hc01, hc13, hlam, hphi, p119_1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h109, hlam, p119_1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [hlam, p119_0]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h0, h109, h111, h113, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p119_1, u2ehi4]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h0, h109, h111, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p119_1, u2ehi4]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p119_1, u4elo0]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h110, hlam, p119_0]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h112, hlam, p119_0]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [hlam, p119_0]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h111, h60, hlam, hphi, ht23, ht34, p119_1, u2ehi4, u4elo1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h0, h111, hc01, hc12, hlam, hphi, p119_1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h111, hlam, p119_1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h113, h60, hc03, hlam, hphi, ht34, p119_1, u4elo1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [h113, hlam, p119_1]
                            · have p119_0 := h119c.1
                              have p119_1 := h119c.2.1
                              have p119_2 := h119c.2.2.1
                              have p119_3 := h119c.2.2.2
                              linarith only [hlam, p119_0]
                          · linarith only [h113, h118, h60, hc34, hlam, hphi, u4elo1]
                        · linarith only [h113, h117, h60, hc24, hlam, hphi, u4elo1]
                      · linarith only [h116, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
                    · linarith only [h0, h115, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]
                  · linarith only [h0, h109, h114, hlam]
                · linarith only [h110, h113, hlam, hphi, ht23, ht34, u2ehi3, u4elo4]
              · linarith only [h109, h112, hlam, hphi, ht23, ht34, u2ehi2, u4elo3]
            · linarith only [h109, h111, hc25, hlam, hphi, u2ehi2]
          · linarith only [h109, h110, hc24, hlam, hphi, u2ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h154 | h154
          · linarith only [h109, h154, hc23, hlam, hphi, u2ehi3]
          · linarith only [h154, hlam, hphi, ht23, ht34, u2ehi0, u4elo2]

theorem r1l7_20_12_14_H_L_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0elo := hb0.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · linarith only [h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
          · linarith only [h0, h2, h5, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
            · linarith only [h0, h2, h4, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
              · linarith only [h9, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                · linarith only [h0, h11, h2, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h11, h2, h4, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h14 | h14
          · linarith only [h1, h14, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h16 | h16
            · linarith only [h1, h16, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h18 | h18
              · linarith only [h18, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h20 | h20
                · linarith only [h0, h18, h2, h20, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h14, h22, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                    · linarith only [h1, h16, h24, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h26 | h26
                      · linarith only [h0, h18, h2, h24, h26, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1, h2, h20, h26, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h29 | h29
      · linarith only [h29, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h31 | h31
        · linarith only [h0, h1, h31, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h33 | h33
          · linarith only [h0, h33, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h35 | h35
            · linarith only [h35, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h37 | h37
              · linarith only [h37, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                · linarith only [h0, h1, h31, h35, h37, h39, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                  · linarith only [h0, h33, h41, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
                    · linarith only [h0, h1, h35, h39, h43, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h43, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h46 | h46
    · rcases m.htr 0 1 4 (by decide) (by decide) with h47 | h47
      · linarith only [h47, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h49 | h49
        · rcases m.htr 0 2 4 (by decide) (by decide) with h50 | h50
          · linarith only [h50, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h52 | h52
            · linarith only [h0, h46, h50, h52, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h54 | h54
              · linarith only [h54, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h56 | h56
                · rcases m.htr 1 2 4 (by decide) (by decide) with h57 | h57
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
                    · linarith only [h0, h46, h50, h52, h54, h58, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h60 | h60
                      · linarith only [h0, h46, h50, h54, h58, h60, hc13, hc34, hlam, hphi]
                      · linarith only [h46, h47, h56, h60, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h63 | h63
                    · linarith only [h0, h46, h50, h54, h63, hlam, hphi, ht0b, ht45, ht5b, u0elo4, u4ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h0, h46, h50, h54, h56, h63, h65, hc23, hc34, hlam, hphi]
                      · linarith only [h46, h47, h56, h65, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h49, h50, h54, h56, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo4]
        · linarith only [h0, h46, h49, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h70 | h70
      · linarith only [h70, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h72 | h72
        · rcases m.htr 0 2 4 (by decide) (by decide) with h73 | h73
          · linarith only [h73, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
            · linarith only [h72, h73, h75, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h77 | h77
              · linarith only [h77, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                · rcases m.htr 1 2 4 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                        · linarith only [h46, h72, h73, h75, h77, h79, h81, h82, h83, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                          · linarith only [h72, h73, h77, h83, h85, hc23, hc34, hlam, hphi]
                          · linarith only [h72, h73, h79, h81, h82, h85, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h72, h73, h80, h82, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h89 | h89
                      · linarith only [h72, h73, h77, h81, h89, hc23, hc34, hlam, hphi]
                      · linarith only [h72, h73, h80, h89, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h92 | h92
                    · linarith only [h46, h75, h79, h80, h92, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                      · linarith only [h72, h73, h77, h92, h94, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                        · linarith only [h72, h96, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                          · linarith only [h70, h94, h96, h98, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h72, h73, h98, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h72, h79, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h102 | h102
          · linarith only [h102, h72, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h104 | h104
            · linarith only [h104, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h106 | h106
              · linarith only [h106, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h108 | h108
                · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h111 | h111
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                        · linarith only [h0, h104, h108, h112, h72, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h108, h110, h112, h72, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                        · linarith only [h0, h104, h108, h115, h72, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h110, h111, h115, h72, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h119 | h119
                        · linarith only [h110, h119, h46, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                          · linarith only [h106, h109, h121, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h102, h118, h121, hc01, hc14, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h124 | h124
                        · linarith only [h0, h104, h108, h124, h72, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h126 | h126
                          · linarith only [h0, h108, h110, h118, h126, h72, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h128 | h128
                            · linarith only [h0, h108, h110, h118, h128, h72, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h108, h110, h128, h72, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h108, h109, h72, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                  · linarith only [h0, h102, h108, h132, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h135 | h135
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h137 | h137
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h106, h134, h138, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                            · linarith only [h0, h104, h135, h138, h72, hc01, hc14, hlam, hphi]
                          · linarith only [h132, h135, h137, hlam]
                        · linarith only [h0, h108, h136, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h143 | h143
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                          · linarith only [h135, h144, h70, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h132, h144, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h134, h143, h72, hc01, hc13, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h148 | h148
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                        · linarith only [h134, h149, h46, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h108, h149, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                        · linarith only [h0, h108, h134, h152, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h108, h152, hc01, hc34, hlam, hphi, ht12, ht23]

end R2N4
