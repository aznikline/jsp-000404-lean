import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_14_M_IR_L_R (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h4ehi := hb4.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                  · linarith only [h0, h4, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14 | h14
                      · linarith only [h0, h14, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h11, h13, h14, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h17, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h17, h19, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h19, h4, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h0, h3, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
            · linarith only [h24, h4, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
              · linarith only [h0, h1, h26, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
                · rcases m.htr 2 3 4 (by decide) (by decide) with h29 | h29
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h30 | h30
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h31 | h31
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h32 | h32
                        · linarith only [h0, h1, h28, h32, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h1, h29, h31, h32, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h24, h31, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · linarith only [h24, h29, h30, hc35, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h29, h4, hc34, hlam, hphi, ht23, u2ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                  · linarith only [h28, h38, h4, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h38, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h2, h3, hc25, hlam, hphi, u2ehi3]
      · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h43 | h43
      · linarith only [h1, h43, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h45 | h45
        · linarith only [h1, h45, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h47 | h47
          · linarith only [h0, h1, h47, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
            · linarith only [h0, h43, h49, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
              · linarith only [h0, h45, h51, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h55 | h55
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h56 | h56
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h57 | h57
                        · rcases h2bigk with h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c | h58c
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h45, h56, hc24, hlam, hphi, p58_1, u2ehi1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h1, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h43, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h45, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h47, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h49, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h51, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hc23, hlam, hphi, p58_1, u2ehi0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hc23, hlam, hphi, p58_1, u2ehi1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hc23, hlam, hphi, p58_1, u2ehi3]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h45, hc23, hlam, hphi, p58_1, u2ehi1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, hc24, hlam, hphi, p58_1, u2ehi1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hc24, hlam, hphi, p58_1, u2ehi1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h54, hlam, p58_1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, h45, h54, hc23, hlam, hphi, p58_1, u2ehi1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h0, hc25, hlam, hphi, p58_1, u2ehi1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hc25, hlam, hphi, p58_1, u2ehi1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h55, hlam, p58_1]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [h56, hlam, p58_0]
                          · have p58_0 := h58c.1
                            have p58_1 := h58c.2.1
                            have p58_2 := h58c.2.2.1
                            have p58_3 := h58c.2.2.2
                            linarith only [hlam, p58_0]
                        · rcases h2bigk with h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h1, hc23, hlam, hphi, p84_1, u2ehi1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h1, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h43, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h45, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h0, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h47, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h49, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h51, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hc23, hlam, hphi, p84_1, u2ehi0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hc23, hlam, hphi, p84_1, u2ehi1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h56, h57, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p84_1, u4ehi3]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hc23, hlam, hphi, p84_1, u2ehi4]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h0, hc24, hlam, hphi, p84_1, u2ehi1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hc24, hlam, hphi, p84_1, u2ehi1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h54, hlam, p84_1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h0, h45, h54, hc23, hlam, hphi, p84_1, u2ehi1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h0, hc25, hlam, hphi, p84_1, u2ehi1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hc25, hlam, hphi, p84_1, u2ehi1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h55, hlam, p84_1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h56, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                      · linarith only [h0, h43, h56, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                    · linarith only [h0, h1, h55, hc35, hlam, hphi, ht23, u2ehi1]
                  · linarith only [h0, h1, h53, h54, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h113 | h113
                  · linarith only [h113, h47, h53, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h1, h113, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h116 | h116
    · rcases m.htr 0 2 4 (by decide) (by decide) with h117 | h117
      · rcases m.htr 0 2 5 (by decide) (by decide) with h118 | h118
        · rcases m.htr 1 2 3 (by decide) (by decide) with h119 | h119
          · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
            · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
              · rcases m.htr 1 3 4 (by decide) (by decide) with h122 | h122
                · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h125 | h125
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h126 | h126
                        · linarith only [h116, h123, h126, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h117, h125, h126, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h129 | h129
                        · linarith only [h125, h129, hc34, hlam, hphi, ht23, u2ehi3]
                        · rcases h2bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h0, hlam, p131_1]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h0, h124, h129, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p131_1, u4ehi3]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            rcases p131_3 (m.d 0 2) (by simp) with h135 | h135
                            · rcases p131_3 (m.d 1 2) (by simp) with h136 | h136
                              · rcases p131_3 (m.d 2 3) (by simp) with h137 | h137
                                · linarith only [h116, h137, hlam]
                                · linarith only [h123, h137, hlam]
                              · linarith only [h120, h136, hlam]
                            · linarith only [h135, hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            rcases p131_3 (m.d 0 2) (by simp) with h142 | h142
                            · rcases p131_3 (m.d 1 2) (by simp) with h143 | h143
                              · rcases p131_3 (m.d 2 3) (by simp) with h144 | h144
                                · linarith only [h116, h144, hlam]
                                · linarith only [h124, h144, hlam]
                              · linarith only [h121, h143, hlam]
                            · linarith only [h142, hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h116, h124, h129, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p131_1, u4ehi3]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h124, h129, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p131_1, u4ehi3]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            rcases p131_3 (m.d 0 2) (by simp) with h152 | h152
                            · linarith only [h0, h152, hlam]
                            · linarith only [h117, h152, hlam]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            rcases p131_3 (m.d 0 2) (by simp) with h155 | h155
                            · linarith only [h0, h155, hlam]
                            · linarith only [h118, h155, hlam]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h116, hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h119, hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h116, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi3]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h0, h116, h125, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi3]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h117, hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h120, hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h123, hlam, p131_1]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h125, hlam, p131_1]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h118, hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h121, hlam, p131_0]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [h124, hlam, p131_1]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [hc25, hlam, hphi, p131_1, u2ehi3]
                          · have p131_0 := h131c.1
                            have p131_1 := h131c.2.1
                            have p131_2 := h131c.2.2.1
                            have p131_3 := h131c.2.2.2
                            linarith only [hlam, p131_0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h173 | h173
                      · linarith only [h123, h124, h173, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h175 | h175
                        · linarith only [h116, h123, h173, h175, hc03, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h123, h124, h175, hc45, hlam, hphi, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h180 | h180
                        · linarith only [h119, h122, h123, h178, h180, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h117, h123, h178, h179, h180, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                      · linarith only [h123, h178, h179, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h184 | h184
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h185 | h185
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
                            linarith only [h0, hlam, p186_1]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            rcases p186_3 (m.d 0 2) (by simp) with h189 | h189
                            · rcases p186_3 (m.d 1 2) (by simp) with h190 | h190
                              · rcases p186_3 (m.d 2 3) (by simp) with h191 | h191
                                · linarith only [h191, hlam, p186_0]
                                · rcases p186_3 (m.d 2 4) (by simp) with h193 | h193
                                  · linarith only [h117, h193, hlam]
                                  · linarith only [h123, h193, hlam]
                              · linarith only [h119, h190, hlam]
                            · linarith only [h189, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h0, h184, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p186_1, u4ehi4]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            rcases p186_3 (m.d 0 2) (by simp) with h199 | h199
                            · rcases p186_3 (m.d 1 2) (by simp) with h200 | h200
                              · rcases p186_3 (m.d 2 3) (by simp) with h201 | h201
                                · linarith only [h116, h201, hlam]
                                · rcases p186_3 (m.d 2 4) (by simp) with h203 | h203
                                  · linarith only [h117, h203, hlam]
                                  · linarith only [h184, h203, hlam]
                              · linarith only [h121, h200, hlam]
                            · linarith only [h199, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h116, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p186_1, u2ehi2]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            rcases p186_3 (m.d 0 2) (by simp) with h210 | h210
                            · linarith only [h0, h210, hlam]
                            · linarith only [h116, h210, hlam]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h184, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p186_1, u4ehi4]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            rcases p186_3 (m.d 0 2) (by simp) with h214 | h214
                            · linarith only [h0, h214, hlam]
                            · linarith only [h118, h214, hlam]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h116, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h119, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h123, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h178, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h117, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h120, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h117, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p186_1, u2ehi2]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h119, h122, h123, h178, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p186_1, u2ehi2]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h118, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h121, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [hc25, hlam, hphi, p186_1, u2ehi2]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [h184, hlam, p186_0]
                          · have p186_0 := h186c.1
                            have p186_1 := h186c.2.1
                            have p186_2 := h186c.2.2.1
                            have p186_3 := h186c.2.2.2
                            linarith only [hlam, p186_0]
                        · linarith only [h123, h185, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h233 | h233
                        · linarith only [h119, h122, h184, h233, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h123, h233, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                  · linarith only [h119, h122, h236, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h239 | h239
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h240 | h240
                        · rcases h2bigk with h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h0, hlam, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h238, h240, hc02, hlam, hphi, ht0b, ht45, ht5b, p241_1, u4ehi4]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h0, h236, h238, h240, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p241_1, u4ehi4]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            rcases p241_3 (m.d 0 2) (by simp) with h246 | h246
                            · rcases p241_3 (m.d 1 2) (by simp) with h247 | h247
                              · rcases p241_3 (m.d 2 3) (by simp) with h248 | h248
                                · linarith only [h116, h248, hlam]
                                · linarith only [h238, h248, hlam]
                              · linarith only [h121, h247, hlam]
                            · linarith only [h246, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h116, h238, h240, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p241_1, u4ehi4]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h238, h240, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p241_1, u4ehi4]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h236, h238, h240, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p241_1, u4ehi4]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            rcases p241_3 (m.d 0 2) (by simp) with h257 | h257
                            · linarith only [h0, h257, hlam]
                            · linarith only [h118, h257, hlam]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h116, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h119, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h236, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h119, h122, hc34, hlam, hphi, ht23, p241_1, u2ehi4]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h117, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h120, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h117, h238, h240, hc02, hlam, hphi, ht0b, ht45, ht5b, p241_1, u4ehi4]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h0, h117, h119, h122, h238, h240, hc12, hc34, hlam, hphi, ht01, ht0b, ht23, ht45, ht5b, p241_1, u2ehi4, u4ehi4]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h118, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h121, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h238, hlam, p241_1]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [h239, hlam, p241_0]
                          · have p241_0 := h241c.1
                            have p241_1 := h241c.2.1
                            have p241_2 := h241c.2.2.1
                            have p241_3 := h241c.2.2.2
                            linarith only [hlam, p241_0]
                        · linarith only [h119, h122, h240, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h236, h238, h239, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h277 | h277
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h278 | h278
                        · rcases h2bigk with h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h0, hlam, p279_1]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            rcases p279_3 (m.d 0 2) (by simp) with h282 | h282
                            · rcases p279_3 (m.d 1 2) (by simp) with h283 | h283
                              · rcases p279_3 (m.d 2 3) (by simp) with h284 | h284
                                · linarith only [h284, hlam, p279_0]
                                · rcases p279_3 (m.d 2 4) (by simp) with h286 | h286
                                  · linarith only [h117, h286, hlam]
                                  · linarith only [h236, h286, hlam]
                              · linarith only [h119, h283, hlam]
                            · linarith only [h282, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h277, hc02, hlam, hphi, ht0b, ht45, ht5b, p279_1, u4ehi4]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            rcases p279_3 (m.d 0 2) (by simp) with h292 | h292
                            · rcases p279_3 (m.d 1 2) (by simp) with h293 | h293
                              · rcases p279_3 (m.d 2 3) (by simp) with h294 | h294
                                · linarith only [h116, h294, hlam]
                                · rcases p279_3 (m.d 2 4) (by simp) with h296 | h296
                                  · linarith only [h117, h296, hlam]
                                  · linarith only [h277, h296, hlam]
                              · linarith only [h121, h293, hlam]
                            · linarith only [h292, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h116, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p279_1, u2ehi2]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            rcases p279_3 (m.d 0 2) (by simp) with h303 | h303
                            · linarith only [h0, h303, hlam]
                            · linarith only [h116, h303, hlam]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h277, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p279_1, u4ehi4]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            rcases p279_3 (m.d 0 2) (by simp) with h307 | h307
                            · linarith only [h0, h307, hlam]
                            · linarith only [h118, h307, hlam]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h116, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h119, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h236, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h238, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h117, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h120, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h117, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p279_1, u2ehi2]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h0, h117, h238, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p279_1, u2ehi2]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h118, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h121, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [hc25, hlam, hphi, p279_1, u2ehi2]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [h277, hlam, p279_0]
                          · have p279_0 := h279c.1
                            have p279_1 := h279c.2.1
                            have p279_2 := h279c.2.2.1
                            have p279_3 := h279c.2.2.2
                            linarith only [hlam, p279_0]
                        · linarith only [h119, h122, h278, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h326 | h326
                        · linarith only [h277, h326, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h119, h122, h326, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h0, h116, h121, hc25, hlam, hphi, u2ehi2]
            · linarith only [h0, h118, h120, hc24, hlam, hphi, u2ehi4]
          · linarith only [h0, h118, h119, hc23, hlam, hphi, u2ehi4]
        · linarith only [h116, h118, hc25, hlam, hphi, u2ehi2]
      · linarith only [h116, h117, hc24, hlam, hphi, u2ehi2]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h334 | h334
      · linarith only [h116, h334, hc23, hlam, hphi, u2ehi3]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h336 | h336
        · linarith only [h116, h336, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h338 | h338
          · rcases m.htr 1 2 4 (by decide) (by decide) with h339 | h339
            · rcases m.htr 1 2 5 (by decide) (by decide) with h340 | h340
              · rcases m.htr 1 3 4 (by decide) (by decide) with h341 | h341
                · rcases m.htr 2 3 4 (by decide) (by decide) with h342 | h342
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h343 | h343
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h344 | h344
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h345 | h345
                        · linarith only [h338, h342, h345, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h338, h342, h344, h345, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h334, h344, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h334, h342, h343, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h116, h342, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h116, h338, h341, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h116, h338, h340, hc25, hlam, hphi, u2ehi0]
            · linarith only [h116, h338, h339, hc24, hlam, hphi, u2ehi0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
            · linarith only [h338, h354, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h356 | h356
              · linarith only [h338, h356, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h358 | h358
                · rcases m.htr 2 3 4 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h360 | h360
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h361 | h361
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h362 | h362
                        · rcases h2bigk with h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, hlam, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h116, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h334, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h336, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h356, h359, h361, hc23, hlam, hphi, p363_1, u2ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h338, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h354, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h356, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hc23, hlam, hphi, p363_1, u2ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hc23, hlam, hphi, p363_1, u2ehi1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hc23, hlam, hphi, p363_1, u2ehi3]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h356, hc01, hc23, hlam, hphi, ht12, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hc24, hlam, hphi, p363_1, u2ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h359, hlam, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h356, h359, hc01, hc23, hlam, hphi, ht12, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hc25, hlam, hphi, p363_1, u2ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h360, hlam, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h361, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                        · rcases h2bigk with h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h0, hlam, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h116, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h334, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h336, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h338, hc23, hlam, hphi, p389_1, u2ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h338, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h354, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h356, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hc23, hlam, hphi, p389_1, u2ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hc23, hlam, hphi, p389_1, u2ehi1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h361, h362, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p389_1, u4ehi3]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hc23, hlam, hphi, p389_1, u2ehi4]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hc24, hlam, hphi, p389_1, u2ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h0, hc01, hc24, hlam, hphi, ht12, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h359, hlam, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h0, h356, h359, hc01, hc23, hlam, hphi, ht12, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hc25, hlam, hphi, p389_1, u2ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h0, hc01, hc25, hlam, hphi, ht12, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h360, hlam, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h361, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hlam, p389_0]
                      · linarith only [h334, h361, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h116, h360, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h0, h338, h359, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h418 | h418
                  · linarith only [h0, h338, h358, h418, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h116, h418, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
