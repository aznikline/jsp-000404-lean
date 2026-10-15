import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_23_L_0_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1elo := hb1.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · linarith only [h0, h5, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
            · linarith only [h0, h2, h5, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
            · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
            · linarith only [h0, h2, h8, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
        · linarith only [h2, h3, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h12 | h12
        · linarith only [h12, h2, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
          · rcases m.htr 1 3 4 (by decide) (by decide) with h15 | h15
            · linarith only [h15, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
              · linarith only [h0, h12, h17, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                · linarith only [h0, h14, h19, h2, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h0, h12, h14, h21, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                    · rcases h3bigk with h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h12, h14, h23, hc34, hlam, hphi, p24_1, u3ehi2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h12, h23, hc34, hlam, hphi, p24_1, u3ehi2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h2, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h12, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h0, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24_1, u1elo2, u3ehi2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h15, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h17, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h1, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h14, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h19, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h21, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hc34, hlam, hphi, p24_1, u3ehi0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h14, hc34, hlam, hphi, p24_1, u3ehi2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hc34, hlam, hphi, p24_1, u3ehi2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hc34, hlam, hphi, p24_1, u3ehi4]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h0, h14, hc35, hlam, hphi, p24_1, u3ehi2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h14, hc35, hlam, hphi, p24_1, u3ehi2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hc35, hlam, hphi, p24_1, u3ehi2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h23, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                    · linarith only [h0, h14, h2, h23, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h51 | h51
            · linarith only [h1, h14, h2, h51, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h53 | h53
              · linarith only [h1, h14, h2, h53, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                · linarith only [h1, h2, h55, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                  · linarith only [h1, h12, h57, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                    · rcases h3bigk with h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h12, h59, hc34, hlam, hphi, p60_1, u3ehi1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h12, h14, h59, hc34, hlam, hphi, p60_1, u3ehi1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h2, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h12, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h0, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h14, hlam, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h51, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h53, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h1, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h1, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p60_1, u3ehi1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h55, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h57, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hc34, hlam, hphi, p60_1, u3ehi0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hc34, hlam, hphi, p60_1, u3ehi1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h14, hc12, hc34, hlam, hphi, ht23, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hc34, hlam, hphi, p60_1, u3ehi4]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h1, h14, hc12, hc35, hlam, hphi, ht23, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hc35, hlam, hphi, p60_1, u3ehi1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h14, hc12, hc35, hlam, hphi, ht23, p60_1]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [h59, hlam, p60_0]
                      · have p60_0 := h60c.1
                        have p60_1 := h60c.2.1
                        have p60_2 := h60c.2.2.1
                        have p60_3 := h60c.2.2.2
                        linarith only [hlam, p60_0]
                    · linarith only [h1, h14, h2, h59, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h87 | h87
      · rcases m.htr 0 3 5 (by decide) (by decide) with h88 | h88
        · rcases m.htr 1 2 3 (by decide) (by decide) with h89 | h89
          · linarith only [h1, h87, h89, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
            · linarith only [h0, h91, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
            · linarith only [h0, h87, h91, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
        · linarith only [h87, h88, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h95 | h95
        · linarith only [h87, h95, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h97 | h97
          · linarith only [h0, h1, h97, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
            · linarith only [h0, h87, h99, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h101 | h101
              · linarith only [h0, h101, h95, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                · rcases m.htr 2 3 5 (by decide) (by decide) with h104 | h104
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h105 | h105
                    · rcases h3bigk with h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h103, h105, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p106_1, u3ehi1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h1, hlam, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h87, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h95, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h0, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h97, hlam, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h99, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h101, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        rcases p106_3 (m.d 0 3) (by simp) with h117 | h117
                        · linarith only [h1, h117, hlam]
                        · rcases p106_3 (m.d 1 3) (by simp) with h119 | h119
                          · linarith only [h119, h97, hlam]
                          · rcases p106_3 (m.d 2 3) (by simp) with h121 | h121
                            · rcases p106_3 (m.d 3 4) (by simp) with h122 | h122
                              · linarith only [h103, h122, hlam]
                              · linarith only [h122, h87, hlam]
                            · linarith only [h1, h121, hlam]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        rcases p106_3 (m.d 0 3) (by simp) with h126 | h126
                        · linarith only [h1, h126, hlam]
                        · linarith only [h0, h126, hlam]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h1, h105, h95, hc02, hc23, hlam, hphi, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h0, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p106_1, u3ehi1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h0, hc34, hlam, hphi, p106_1, u3ehi1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hc34, hlam, hphi, p106_1, u3ehi1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h103, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h0, h103, h95, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p106_1, u3ehi1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h0, hc35, hlam, hphi, p106_1, u3ehi1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hc35, hlam, hphi, p106_1, u3ehi1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h104, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h105, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                    · linarith only [h0, h105, h87, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h0, h103, h104, h87, hc35, hlam, hphi, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h144 | h144
                  · linarith only [h103, h144, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
                    · rcases h3bigk with h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c | h147c
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h1, h144, h146, hc34, hlam, hphi, p147_1, u3ehi1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h1, hlam, p147_1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h87, hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h95, hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h0, hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h97, hlam, p147_1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h99, hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h101, hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h144, h146, hc34, hlam, hphi, p147_1, u3ehi0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h144, h146, hc34, hlam, hphi, p147_1, u3ehi1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h103, hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h144, hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h0, hc34, hlam, hphi, p147_1, u3ehi1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [hc34, hlam, hphi, p147_1, u3ehi1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h1, hc02, hc34, hlam, hphi, ht23, p147_1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [hc34, hlam, hphi, p147_1, u3ehi4]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h0, hc35, hlam, hphi, p147_1, u3ehi1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [hc35, hlam, hphi, p147_1, u3ehi1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h0, h1, hc35, hlam, hphi, p147_1, u3ehi1]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [h146, hlam, p147_0]
                      · have p147_0 := h147c.1
                        have p147_1 := h147c.2.1
                        have p147_2 := h147c.2.2.1
                        have p147_3 := h147c.2.2.2
                        linarith only [hlam, p147_0]
                    · linarith only [h0, h146, h87, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h174 | h174
    · rcases m.htr 0 3 4 (by decide) (by decide) with h175 | h175
      · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
        · rcases m.htr 1 2 3 (by decide) (by decide) with h177 | h177
          · rcases m.htr 1 3 4 (by decide) (by decide) with h178 | h178
            · rcases m.htr 1 3 5 (by decide) (by decide) with h179 | h179
              · rcases m.htr 2 3 4 (by decide) (by decide) with h180 | h180
                · linarith only [h177, h180, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
                · linarith only [h0, h175, h177, h180, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi2]
              · linarith only [h0, h176, h179, hlam]
            · linarith only [h0, h175, h178, hlam]
          · linarith only [h0, h174, h177, hlam]
        · linarith only [h175, h176, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h187 | h187
        · linarith only [h175, h187, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
          · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
            · linarith only [h175, h190, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h192 | h192
              · linarith only [h174, h187, h190, h192, hc34, hlam, hphi, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                · linarith only [h0, h174, h190, h194, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h196 | h196
                  · linarith only [h0, h189, h192, h196, hc01, hlam, hphi, u1elo1]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
                    · rcases h3bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h0, hlam, p199_1]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p199_1, u1elo2, u3ehi2]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h175, hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h187, hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p199_1, u1elo2, u3ehi0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h192, h198, hc34, hlam, hphi, p199_1, u3ehi2]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h190, hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h192, hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h174, hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h189, hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h194, hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h196, hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h174, hc34, hlam, hphi, p199_1, u3ehi2]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p199_1]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [hc34, hlam, hphi, p199_1, u3ehi2]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [hc34, hlam, hphi, p199_1, u3ehi4]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h174, hc35, hlam, hphi, p199_1, u3ehi2]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p199_1]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [hc35, hlam, hphi, p199_1, u3ehi2]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [h198, hlam, p199_0]
                      · have p199_0 := h199c.1
                        have p199_1 := h199c.2.1
                        have p199_2 := h199c.2.2.1
                        have p199_3 := h199c.2.2.2
                        linarith only [hlam, p199_0]
                    · linarith only [h174, h175, h198, hc45, hlam, hphi, ht34, u3ehi2]
          · linarith only [h0, h174, h189, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h227 | h227
      · rcases m.htr 0 3 5 (by decide) (by decide) with h228 | h228
        · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
          · linarith only [h174, h227, h229, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h231 | h231
            · rcases m.htr 1 3 5 (by decide) (by decide) with h232 | h232
              · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                · rcases m.htr 2 3 5 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h235 | h235
                    · rcases h3bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h0, hlam, p236_1]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h174, hlam, p236_1]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h0, h235, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p236_1, u1elo2, u3ehi4]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p236_1, u1elo2, u3ehi4]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p236_1, u1elo2, u3ehi0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h229, hlam, p236_1]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h235, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p236_1, u1elo2, u3ehi4]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p236_1, u1elo2, u3ehi4]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h227, h235, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p236_1, u3ehi4]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p236_1]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        rcases p236_3 (m.d 0 3) (by simp) with h250 | h250
                        · linarith only [h174, h250, hlam]
                        · linarith only [h227, h250, hlam]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        rcases p236_3 (m.d 0 3) (by simp) with h253 | h253
                        · linarith only [h174, h253, hlam]
                        · linarith only [h228, h253, hlam]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h227, hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h231, hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h233, hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h227, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p236_1, u3ehi4]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h228, hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h232, hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h234, hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [h235, hlam, p236_0]
                      · have p236_0 := h236c.1
                        have p236_1 := h236c.2.1
                        have p236_2 := h236c.2.2.1
                        have p236_3 := h236c.2.2.2
                        linarith only [hlam, p236_0]
                    · rcases h3bigk with h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c | h266c
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h0, hlam, p266_1]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h174, hlam, p266_1]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p266_1, u1elo2, u3ehi3]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p266_1, u1elo2, u3ehi4]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p266_1, u1elo2, u3ehi0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h229, hlam, p266_1]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p266_1, u1elo2, u3ehi3]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p266_1, u1elo2, u3ehi4]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h227, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p266_1, u3ehi3]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p266_1]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        rcases p266_3 (m.d 0 3) (by simp) with h280 | h280
                        · linarith only [h174, h280, hlam]
                        · linarith only [h227, h280, hlam]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        rcases p266_3 (m.d 0 3) (by simp) with h283 | h283
                        · linarith only [h174, h283, hlam]
                        · linarith only [h228, h283, hlam]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h227, hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h231, hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h233, hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h235, hlam, p266_1]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h228, hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h232, hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h234, hlam, p266_0]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [h228, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p266_1, u3ehi3]
                      · have p266_0 := h266c.1
                        have p266_1 := h266c.2.1
                        have p266_2 := h266c.2.2.1
                        have p266_3 := h266c.2.2.2
                        linarith only [hlam, p266_0]
                  · linarith only [h0, h228, h229, h234, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · linarith only [h0, h228, h229, h233, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h228, h232, hlam]
            · linarith only [h0, h227, h231, hlam]
        · linarith only [h227, h228, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h301 | h301
        · linarith only [h227, h301, hc34, hlam, hphi, u3ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
          · rcases m.htr 1 3 4 (by decide) (by decide) with h304 | h304
            · linarith only [h227, h304, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h306 | h306
              · linarith only [h301, h304, h306, hc34, hlam, hphi, u3ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                · linarith only [h303, h304, h308, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
                  · linarith only [h0, h303, h306, h310, hc01, hlam, hphi, u1elo1]
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
                        linarith only [h0, hlam, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h174, hlam, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h227, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h301, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p313_1, u1elo2, u3ehi0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h174, h306, h312, hc02, hc34, hlam, hphi, ht23, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h304, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h306, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h303, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p313_1, u1elo1, u3ehi0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h303, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h308, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h310, hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hc34, hlam, hphi, p313_1, u3ehi0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hc34, hlam, hphi, p313_1, u3ehi2]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hlam, p313_0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hc34, hlam, hphi, p313_1, u3ehi4]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [hc35, hlam, hphi, p313_1, u3ehi0]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p313_1]
                      · have p313_0 := h313c.1
                        have p313_1 := h313c.2.1
                        have p313_2 := h313c.2.2.1
                        have p313_3 := h313c.2.2.2
                        linarith only [h174, hc02, hc35, hlam, hphi, ht23, p313_1]
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
                    · linarith only [h227, h312, hc45, hlam, hphi, ht34, u3ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
            · linarith only [h227, h340, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h342 | h342
              · linarith only [h340, h342, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h344 | h344
                · linarith only [h0, h340, h344, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h346 | h346
                  · linarith only [h0, h342, h346, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h348 | h348
                    · rcases h3bigk with h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h0, hlam, p349_1]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h174, hlam, p349_1]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h227, hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h301, hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p349_1, u1elo2, u3ehi0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h303, hlam, p349_1]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h340, hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h342, hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h346, h348, hc34, hlam, hphi, p349_1, u3ehi0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h346, h348, hc34, hlam, hphi, p349_1, u3ehi1]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h344, hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h346, hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [hc34, hlam, hphi, p349_1, u3ehi0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h0, hc01, hc34, hlam, hphi, ht12, ht23, p349_1]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h303, hc12, hc34, hlam, hphi, ht23, p349_1]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [hc34, hlam, hphi, p349_1, u3ehi4]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [hc35, hlam, hphi, p349_1, u3ehi0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h0, hc01, hc35, hlam, hphi, ht12, ht23, p349_1]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h0, h303, hc01, hc35, hlam, hphi, ht12, ht23, p349_1]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [h348, hlam, p349_0]
                      · have p349_0 := h349c.1
                        have p349_1 := h349c.2.1
                        have p349_2 := h349c.2.2.1
                        have p349_3 := h349c.2.2.2
                        linarith only [hlam, p349_0]
                    · linarith only [h227, h348, hc45, hlam, hphi, ht34, u3ehi0]

theorem r1l7_11_23_L_0_M_LI (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1elo := hb1.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h4, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h0, h4, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · linarith only [h3, h5, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                · linarith only [h11, h12, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h14, h4, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h11, h14, h5, hc23, hlam, hphi, u3elo3]
              · linarith only [h11, h3, hc13, hlam, hphi, u3elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
            · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
              · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                · rcases m.htr 2 3 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h1, h18, h22, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases h3bigk with h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c | h24c
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hc13, hlam, hphi, p24_1, u3elo0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h4, hc12, hlam, hphi, ht23, p24_1, u3elo0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        rcases p24_3 (m.d 0 3) (by simp) with h28 | h28
                        · rcases p24_3 (m.d 1 3) (by simp) with h29 | h29
                          · linarith only [h1, h29, hlam]
                          · linarith only [h18, h29, hlam]
                        · linarith only [h28, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        rcases p24_3 (m.d 0 3) (by simp) with h33 | h33
                        · rcases p24_3 (m.d 1 3) (by simp) with h34 | h34
                          · linarith only [h1, h34, hlam]
                          · linarith only [h19, h34, hlam]
                        · linarith only [h33, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h1, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h4, hlam, p24_1]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24_1, u1elo0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h0, h2, h22, h4, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24_1, u1elo0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h2, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h0, h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24_1, u1elo0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h0, h2, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24_1, u1elo0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h0, h2, h22, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24_1, u1elo0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h19, h22, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p24_1, u1elo2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h18, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h20, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h22, hlam, p24_1]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h3, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h19, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h21, hlam, p24_0]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [h19, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p24_1, u1elo2]
                      · have p24_0 := h24c.1
                        have p24_1 := h24c.2.1
                        have p24_2 := h24c.2.2.1
                        have p24_3 := h24c.2.2.2
                        linarith only [hlam, p24_0]
                  · linarith only [h19, h21, h4, hlam]
                · linarith only [h20, h4, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h19, h3, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h61 | h61
              · rcases m.htr 2 3 4 (by decide) (by decide) with h62 | h62
                · linarith only [h0, h18, h2, h61, h62, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                · linarith only [h4, h62, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h3, h61, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h66 | h66
          · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
            · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
              · linarith only [h1, h3, h68, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                · linarith only [h0, h66, h70, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · linarith only [h1, h3, h67, h70, hc23, hlam, hphi, u3elo4]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h73 | h73
              · linarith only [h3, h67, h73, hc03, hlam, hphi, u3elo3]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                · linarith only [h0, h66, h75, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                  · linarith only [h1, h3, h66, h77, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                    · rcases h3bigk with h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c | h80c
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h3, h79, hc13, hlam, hphi, p80_1, u3elo3]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h3, h79, hc23, hlam, hphi, p80_1, u3elo3]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h3, h79, hlam, p80_1]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h3, hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h1, hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [hc23, hlam, hphi, p80_1, u3elo1]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h67, hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h73, hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h2, hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h66, hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h75, hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h77, hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [hc03, hlam, hphi, p80_1, u3elo3]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h66, hc23, hlam, hphi, p80_1, u3elo3]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [hc23, hlam, hphi, p80_1, u3elo3]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h1, h3, h66, hc23, hlam, hphi, p80_1, u3elo3]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h1, h66, hc23, hlam, hphi, p80_1, u3elo4]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h66, hc23, hlam, hphi, p80_1, u3elo4]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [hc23, hlam, hphi, p80_1, u3elo4]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [h79, hlam, p80_0]
                      · have p80_0 := h80c.1
                        have p80_1 := h80c.2.1
                        have p80_2 := h80c.2.2.1
                        have p80_3 := h80c.2.2.2
                        linarith only [hlam, p80_0]
                    · rcases h3bigk with h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c | h106c
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h66, hc23, hlam, hphi, p106_1, u3elo0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hc23, hlam, hphi, p106_1, u3elo0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h3, h75, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p106_1, u3elo4]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h3, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h1, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hc23, hlam, hphi, p106_1, u3elo1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h67, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h73, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h2, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h66, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h75, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h77, hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h79, hc03, hc45, hlam, hphi, ht34, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h66, h79, hc23, hc45, hlam, hphi, ht34, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h79, hc23, hc45, hlam, hphi, ht34, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h79, hlam, p106_1]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h1, h66, hc23, hlam, hphi, p106_1, u3elo4]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h66, hc23, hlam, hphi, p106_1, u3elo4]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hc23, hlam, hphi, p106_1, u3elo4]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [h66, h67, hc23, hlam, hphi, p106_1, u3elo4]
                      · have p106_0 := h106c.1
                        have p106_1 := h106c.2.1
                        have p106_2 := h106c.2.2.1
                        have p106_3 := h106c.2.2.2
                        linarith only [hlam, p106_0]
          · linarith only [h2, h3, h66, hc12, hlam, hphi, ht23, u3elo4]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
        · rcases m.htr 1 2 3 (by decide) (by decide) with h134 | h134
          · linarith only [h0, h134, h2, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
            · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
              · rcases m.htr 2 3 4 (by decide) (by decide) with h138 | h138
                · rcases m.htr 2 3 5 (by decide) (by decide) with h139 | h139
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h140 | h140
                    · linarith only [h1, h136, h140, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · rcases h3bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h2, hc13, hlam, hphi, p142_1, u3elo2]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h2, hlam, p142_1]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        rcases p142_3 (m.d 0 3) (by simp) with h146 | h146
                        · rcases p142_3 (m.d 1 3) (by simp) with h147 | h147
                          · linarith only [h1, h147, hlam]
                          · linarith only [h136, h147, hlam]
                        · linarith only [h146, hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        rcases p142_3 (m.d 0 3) (by simp) with h151 | h151
                        · rcases p142_3 (m.d 1 3) (by simp) with h152 | h152
                          · linarith only [h1, h152, hlam]
                          · linarith only [h137, h152, hlam]
                        · linarith only [h151, hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h1, hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h134, hlam, p142_1]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h1, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1, u1elo0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h1, h140, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1, u1elo0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [hc03, hlam, hphi, p142_1, u3elo2]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [hc13, hlam, hphi, p142_1, u3elo2]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        rcases p142_3 (m.d 0 3) (by simp) with h164 | h164
                        · linarith only [h164, h2, hlam]
                        · linarith only [h1, h137, h140, h164, hlam]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        rcases p142_3 (m.d 0 3) (by simp) with h167 | h167
                        · linarith only [h167, h2, hlam]
                        · linarith only [h133, h167, hlam]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h1, h137, h140, hlam, p142_1]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h136, hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h138, hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h140, hlam, p142_1]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h133, hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h137, hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h139, hlam, p142_0]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [h137, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1, u1elo2]
                      · have p142_0 := h142c.1
                        have p142_1 := h142c.2.1
                        have p142_2 := h142c.2.2.1
                        have p142_3 := h142c.2.2.2
                        linarith only [hlam, p142_0]
                  · linarith only [h1, h137, h139, h2, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · linarith only [h0, h136, h138, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
              · linarith only [h133, h137, h2, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
              · rcases m.htr 2 3 4 (by decide) (by decide) with h184 | h184
                · linarith only [h136, h183, h184, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h0, h184, h2, hc12, hlam, hphi, ht23, u3elo3]
              · linarith only [h133, h183, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
          · linarith only [h0, h188, h2, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h190 | h190
            · rcases m.htr 1 3 5 (by decide) (by decide) with h191 | h191
              · linarith only [h133, h191, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                  · linarith only [h1, h133, h190, h194, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                  · linarith only [h0, h194, h2, hc12, hlam, hphi, ht23, u3elo4]
                · linarith only [h0, h190, h193, h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h198 | h198
              · linarith only [h1, h133, h198, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h200 | h200
                · linarith only [h190, h200, hc13, hlam, hphi, u3elo2]
                · linarith only [h0, h2, h200, hc12, hlam, hphi, ht23, u3elo3]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h204 | h204
    · rcases m.htr 0 2 3 (by decide) (by decide) with h205 | h205
      · rcases m.htr 0 3 5 (by decide) (by decide) with h206 | h206
        · rcases m.htr 1 2 3 (by decide) (by decide) with h207 | h207
          · rcases m.htr 1 3 4 (by decide) (by decide) with h208 | h208
            · linarith only [h0, h204, h208, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h210 | h210
              · linarith only [h0, h204, h210, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
              · linarith only [h206, h210, hc13, hlam, hphi, u3elo0]
          · linarith only [h0, h207, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h214 | h214
          · rcases m.htr 1 3 4 (by decide) (by decide) with h215 | h215
            · linarith only [h0, h204, h215, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h217 | h217
              · linarith only [h0, h204, h206, h217, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h219 | h219
                · linarith only [h214, h215, h219, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h221 | h221
                  · linarith only [h204, h206, h214, h221, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h223 | h223
                    · rcases h3bigk with h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c | h224c
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h206, h223, hc13, hlam, hphi, p224_1, u3elo3]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h206, h223, hc23, hlam, hphi, p224_1, u3elo3]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h206, h223, hlam, p224_1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h206, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h204, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h0, h204, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p224_1, u1elo1]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h215, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h217, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h205, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h214, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h219, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h221, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hc03, hlam, hphi, p224_1, u3elo3]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hc13, hlam, hphi, p224_1, u3elo3]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hc23, hlam, hphi, p224_1, u3elo3]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h204, h206, h214, hc23, hlam, hphi, p224_1, u3elo3]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h204, h214, hc23, hlam, hphi, p224_1, u3elo4]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h214, hc23, hlam, hphi, p224_1, u3elo4]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hc23, hlam, hphi, p224_1, u3elo4]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [h223, hlam, p224_0]
                      · have p224_0 := h224c.1
                        have p224_1 := h224c.2.1
                        have p224_2 := h224c.2.2.1
                        have p224_3 := h224c.2.2.2
                        linarith only [hlam, p224_0]
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
                        linarith only [h214, hc23, hlam, hphi, p250_1, u3elo0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h0, h204, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p250_1, u1elo1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h206, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p250_1, u3elo4]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h206, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h204, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h215, hc23, hlam, hphi, p250_1, u3elo3]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h215, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h217, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h205, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h214, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h219, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h221, hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h223, hc03, hc45, hlam, hphi, ht34, p250_1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h223, hc13, hc45, hlam, hphi, ht34, p250_1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h223, hc23, hc45, hlam, hphi, ht34, p250_1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hlam, p250_0]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h223, hlam, p250_1]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h204, h214, hc23, hlam, hphi, p250_1, u3elo4]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h214, hc23, hlam, hphi, p250_1, u3elo4]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hc23, hlam, hphi, p250_1, u3elo4]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [h214, h215, hc23, hlam, hphi, p250_1, u3elo4]
                      · have p250_0 := h250c.1
                        have p250_1 := h250c.2.1
                        have p250_2 := h250c.2.2.1
                        have p250_3 := h250c.2.2.2
                        linarith only [hlam, p250_0]
          · linarith only [h0, h214, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · linarith only [h0, h204, h205, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h278 | h278
      · rcases m.htr 0 3 5 (by decide) (by decide) with h279 | h279
        · rcases m.htr 1 2 3 (by decide) (by decide) with h280 | h280
          · rcases m.htr 1 3 4 (by decide) (by decide) with h281 | h281
            · rcases m.htr 1 3 5 (by decide) (by decide) with h282 | h282
              · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                · rcases m.htr 2 3 5 (by decide) (by decide) with h284 | h284
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h285 | h285
                    · linarith only [h0, h278, h283, h285, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                    · rcases h3bigk with h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c | h287c
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h204, hlam, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hc23, hlam, hphi, p287_1, u3elo0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        rcases p287_3 (m.d 0 3) (by simp) with h291 | h291
                        · rcases p287_3 (m.d 1 3) (by simp) with h292 | h292
                          · rcases p287_3 (m.d 2 3) (by simp) with h293 | h293
                            · linarith only [h278, h293, hlam]
                            · linarith only [h283, h293, hlam]
                          · linarith only [h281, h292, hlam]
                        · linarith only [h291, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        rcases p287_3 (m.d 0 3) (by simp) with h298 | h298
                        · rcases p287_3 (m.d 1 3) (by simp) with h299 | h299
                          · rcases p287_3 (m.d 2 3) (by simp) with h300 | h300
                            · linarith only [h278, h300, hlam]
                            · linarith only [h284, h300, hlam]
                          · linarith only [h282, h299, hlam]
                        · linarith only [h298, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hc03, hlam, hphi, p287_1, u3elo1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h284, h285, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p287_1, u3elo1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        rcases p287_3 (m.d 0 3) (by simp) with h308 | h308
                        · linarith only [h204, h308, hlam]
                        · linarith only [h278, h284, h285, h308, hlam]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        rcases p287_3 (m.d 0 3) (by simp) with h311 | h311
                        · linarith only [h204, h311, hlam]
                        · linarith only [h279, h311, hlam]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h278, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h280, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h0, h278, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p287_1, u1elo1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h0, h278, h285, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p287_1, u1elo1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h278, hc23, hlam, hphi, p287_1, u3elo3]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h281, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h283, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h285, hlam, p287_1]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h279, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h282, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h284, hlam, p287_0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [h279, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p287_1, u3elo0]
                      · have p287_0 := h287c.1
                        have p287_1 := h287c.2.1
                        have p287_2 := h287c.2.2.1
                        have p287_3 := h287c.2.2.2
                        linarith only [hlam, p287_0]
                  · linarith only [h204, h279, h283, h284, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                · linarith only [h281, h283, hc23, hlam, hphi, u3elo1]
              · linarith only [h204, h279, h282, hlam]
            · linarith only [h204, h281, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h280, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h334 | h334
          · rcases m.htr 1 3 4 (by decide) (by decide) with h335 | h335
            · rcases m.htr 1 3 5 (by decide) (by decide) with h336 | h336
              · linarith only [h279, h336, hc03, hlam, hphi, u3elo1]
              · linarith only [h204, h336, hc01, hlam, hphi, ht12, ht23, u3elo4]
            · linarith only [h204, h335, hc01, hlam, hphi, ht12, ht23, u3elo3]
          · linarith only [h0, h278, h334, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h341 | h341
        · rcases m.htr 1 2 3 (by decide) (by decide) with h342 | h342
          · linarith only [h0, h278, h342, hc01, hlam, hphi, u1elo1]
          · linarith only [h0, h342, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h345 | h345
          · linarith only [h0, h278, h345, hc01, hlam, hphi, u1elo1]
          · linarith only [h0, h345, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
