import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_I_L_0_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc13 := m.hcor 1 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h6, h9, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                    · linarith only [h2, h4, h9, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi2]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · linarith only [h2, h4, h7, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi1]
              · linarith only [h2, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h4, h5, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16 | h16
            · linarith only [h16, h4, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
              · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
                · linarith only [h1, h19, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                  · linarith only [h1, h16, h21, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                    · linarith only [h1, h18, h23, h4, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                      · linarith only [h1, h16, h18, h25, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                        · rcases h3bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h16, h18, h27, hc34, hlam, hphi, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h16, h27, hc34, hlam, hphi, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h4, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h16, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h1, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h19, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h21, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h2, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h18, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h23, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h25, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hc34, hlam, hphi, p28_1, u3ehi0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h18, hc34, hlam, hphi, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hc34, hlam, hphi, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hc34, hlam, hphi, p28_1, u3ehi4]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h1, h18, hc35, hlam, hphi, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h18, hc35, hlam, hphi, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hc35, hlam, hphi, p28_1, u3ehi2]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [h27, hlam, p28_0]
                          · have p28_0 := h28c.1
                            have p28_1 := h28c.2.1
                            have p28_2 := h28c.2.2.1
                            have p28_3 := h28c.2.2.2
                            linarith only [hlam, p28_0]
                        · linarith only [h1, h18, h27, h4, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h18, h2, hc12, hlam, hphi, u2elo0]
        · linarith only [h2, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h57 | h57
        · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
          · rcases m.htr 0 3 5 (by decide) (by decide) with h59 | h59
            · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
              · linarith only [h2, h60, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h2, h57, h65, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
                      · linarith only [h1, h2, h62, h65, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1, h2, h62, h64, hlam]
                  · linarith only [h62, h63, hc35, hlam, hphi, u3ehi3]
                · linarith only [h2, h58, h62, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
            · linarith only [h58, h59, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h72 | h72
            · linarith only [h58, h72, hc34, hlam, hphi, u3ehi4]
            · linarith only [h2, h57, h72, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h75 | h75
          · rcases m.htr 0 3 5 (by decide) (by decide) with h76 | h76
            · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
              · linarith only [h0, h2, h77, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                · rcases m.htr 1 3 5 (by decide) (by decide) with h80 | h80
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h83 | h83
                        · rcases h3bigk with h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c | h84c
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h79, h83, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p84_1, u3ehi4]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h2, hlam, p84_1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h2, h83, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p84_1, u2elo2, u3ehi4]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p84_1, u2elo2, u3ehi4]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h1, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h77, hlam, p84_1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h1, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p84_1, u3ehi4]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h1, h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p84_1, u2elo2, u3ehi4]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p84_1, u2elo2, u3ehi0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p84_1, u2elo2, u3ehi1]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h83, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p84_1, u2elo2, u3ehi4]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p84_1, u2elo2, u3ehi4]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h75, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h79, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h81, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h1, h79, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p84_1, u3ehi4]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h76, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h80, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h82, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [h83, hlam, p84_0]
                          · have p84_0 := h84c.1
                            have p84_1 := h84c.2.1
                            have p84_2 := h84c.2.2.1
                            have p84_3 := h84c.2.2.2
                            linarith only [hlam, p84_0]
                        · rcases h3bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo2, u3ehi1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h2, hlam, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h2, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo2, u3ehi3]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h2, h83, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo2, u3ehi3]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h1, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h77, hlam, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p110_1, u3ehi3]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h1, h2, h83, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo2, u3ehi3]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo2, u3ehi0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo2, u3ehi1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo2, u3ehi3]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h83, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p110_1, u2elo2, u3ehi3]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h75, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h79, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h81, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h83, hlam, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h76, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h80, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h82, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h1, h80, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p110_1, u3ehi3]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                      · linarith only [h1, h2, h80, h82, hlam]
                    · linarith only [h1, h2, h80, h81, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h79, h80, hc35, hlam, hphi, u3ehi3]
                · linarith only [h2, h75, h79, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
            · linarith only [h75, h76, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h141 | h141
            · linarith only [h141, h75, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
              · linarith only [h0, h143, h2, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h145 | h145
                · linarith only [h1, h145, h75, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                  · linarith only [h1, h147, h75, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                    · linarith only [h149, h2, h75, hc02, hlam, hphi, u2elo2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h151 | h151
                      · linarith only [h1, h141, h151, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h153 | h153
                        · rcases h3bigk with h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c | h154c
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h151, h153, h2, hc34, hlam, hphi, p154_1, u3ehi1]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h2, hlam, p154_1]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h75, hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h141, hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h1, hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h143, hlam, p154_1]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h145, hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h147, hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h151, h153, hc34, hlam, hphi, p154_1, u3ehi0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h151, h153, hc34, hlam, hphi, p154_1, u3ehi1]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h149, hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h151, hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h1, hc34, hlam, hphi, p154_1, u3ehi1]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [hc34, hlam, hphi, p154_1, u3ehi1]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [hc34, hlam, hphi, p154_1, u3ehi2]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [hc34, hlam, hphi, p154_1, u3ehi4]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h1, hc35, hlam, hphi, p154_1, u3ehi1]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [hc35, hlam, hphi, p154_1, u3ehi1]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h0, h2, hc12, hc35, hlam, hphi, ht23, p154_1]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [h153, hlam, p154_0]
                          · have p154_0 := h154c.1
                            have p154_1 := h154c.2.1
                            have p154_2 := h154c.2.2.1
                            have p154_3 := h154c.2.2.2
                            linarith only [hlam, p154_0]
                        · linarith only [h1, h153, h75, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h181 | h181
      · linarith only [h0, h1, h181, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h183 | h183
        · rcases m.htr 0 3 4 (by decide) (by decide) with h184 | h184
          · rcases m.htr 0 3 5 (by decide) (by decide) with h185 | h185
            · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
              · linarith only [h181, h186, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1, h186, hc12, hlam, hphi, u2elo2]
            · linarith only [h184, h185, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h190 | h190
            · linarith only [h184, h190, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h1, h183, h190, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h193 | h193
          · rcases m.htr 0 3 5 (by decide) (by decide) with h194 | h194
            · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
              · linarith only [h181, h195, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1, h195, hc12, hlam, hphi, u2elo2]
            · linarith only [h193, h194, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h199 | h199
            · linarith only [h193, h199, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h201 | h201
              · linarith only [h0, h1, h201, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1, h201, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h204 | h204
    · linarith only [h0, h204, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h206 | h206
      · rcases m.htr 0 2 5 (by decide) (by decide) with h207 | h207
        · rcases m.htr 0 3 4 (by decide) (by decide) with h208 | h208
          · rcases m.htr 0 3 5 (by decide) (by decide) with h209 | h209
            · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
              · rcases m.htr 1 3 4 (by decide) (by decide) with h211 | h211
                · rcases m.htr 1 3 5 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h213 | h213
                    · linarith only [h206, h213, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0, u3ehi3]
                    · linarith only [h204, h208, h210, h213, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                  · linarith only [h204, h209, h212, hlam]
                · linarith only [h204, h208, h211, hlam]
              · linarith only [h0, h210, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h208, h209, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h220 | h220
            · linarith only [h208, h220, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
              · rcases m.htr 1 3 4 (by decide) (by decide) with h223 | h223
                · linarith only [h208, h222, h223, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h225 | h225
                  · linarith only [h206, h220, h223, h225, hc34, hlam, hphi, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h227 | h227
                    · linarith only [h206, h223, h227, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h229 | h229
                      · linarith only [h0, h204, h206, h225, h229, hc01, hlam, hphi, ht12, u2elo1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h231 | h231
                        · rcases h3bigk with h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c | h232c
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h204, hlam, p232_1]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h204, h225, h231, hc34, hlam, hphi, p232_1, u3ehi2]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h208, hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h220, hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h225, h231, hc34, hlam, hphi, p232_1, u3ehi0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h225, h231, hc34, hlam, hphi, p232_1, u3ehi2]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h223, hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h225, hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h206, hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h222, hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h227, hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h229, hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h206, hc34, hlam, hphi, p232_1, u3ehi2]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [hc34, hlam, hphi, p232_1, u3ehi1]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [hc34, hlam, hphi, p232_1, u3ehi2]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [hc34, hlam, hphi, p232_1, u3ehi4]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h206, hc35, hlam, hphi, p232_1, u3ehi2]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h0, h204, h206, hc01, hc35, hlam, hphi, ht12, p232_1, u2elo1, u3ehi2]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [hc35, hlam, hphi, p232_1, u3ehi2]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [h231, hlam, p232_0]
                          · have p232_0 := h232c.1
                            have p232_1 := h232c.2.1
                            have p232_2 := h232c.2.2.1
                            have p232_3 := h232c.2.2.2
                            linarith only [hlam, p232_0]
                        · linarith only [h206, h208, h231, hc45, hlam, hphi, ht34, u3ehi2]
              · linarith only [h0, h222, hc01, hlam, hphi, ht12, u2elo2]
        · linarith only [h206, h207, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h261 | h261
        · rcases m.htr 0 3 4 (by decide) (by decide) with h262 | h262
          · rcases m.htr 0 3 5 (by decide) (by decide) with h263 | h263
            · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
              · linarith only [h206, h264, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h264, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h262, h263, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h268 | h268
            · linarith only [h262, h268, hc34, hlam, hphi, u3ehi4]
            · linarith only [h206, h261, h268, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h271 | h271
          · rcases m.htr 0 3 5 (by decide) (by decide) with h272 | h272
            · rcases m.htr 1 2 3 (by decide) (by decide) with h273 | h273
              · linarith only [h206, h273, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h273, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h271, h272, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h277 | h277
            · linarith only [h271, h277, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h279 | h279
              · linarith only [h206, h279, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h279, hc01, hlam, hphi, ht12, u2elo2]

theorem r1l7_10_12_23_L_I_L_I_H_L (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_L m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3elo := hb3.1
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
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14 | h14
                              · linarith only [h1, h12, h14, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo0]
                              · linarith only [h14, h6, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · linarith only [h13, hc23, hlam, hphi, u3elo4]
                          · linarith only [h12, hc23, hlam, hphi, u3elo3]
                        · linarith only [h11, h6, hc13, hlam, hphi, u3elo0]
                      · linarith only [h10, h4, h6, hc12, hlam, hphi, ht23, u3elo0]
                    · linarith only [h9, hc12, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                              · linarith only [h1, h22, h25, h27, h8, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                              · rcases h0bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h22, h26, hc01, hc35, hlam, hphi, ht0b, ht5b, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 1) (by simp) with h32 | h32
                                  · rcases p29_3 (m.d 0 2) (by simp) with h33 | h33
                                    · linarith only [h0, h33, hlam]
                                    · linarith only [h3, h33, hlam]
                                  · linarith only [h1, h32, hlam]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 1) (by simp) with h37 | h37
                                  · rcases p29_3 (m.d 0 2) (by simp) with h38 | h38
                                    · linarith only [h0, h38, hlam]
                                    · linarith only [h38, h4, hlam]
                                  · linarith only [h2, h37, hlam]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 1) (by simp) with h42 | h42
                                  · rcases p29_3 (m.d 0 2) (by simp) with h43 | h43
                                    · linarith only [h0, h43, hlam]
                                    · linarith only [h43, h5, hlam]
                                  · linarith only [h42, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 1) (by simp) with h49 | h49
                                  · rcases p29_3 (m.d 0 2) (by simp) with h50 | h50
                                    · rcases p29_3 (m.d 0 3) (by simp) with h51 | h51
                                      · linarith only [h3, h51, hlam]
                                      · rcases p29_3 (m.d 0 4) (by simp) with h53 | h53
                                        · linarith only [h4, h53, hlam]
                                        · rcases p29_3 (m.d 0 5) (by simp) with h55 | h55
                                          · linarith only [h5, h55, hlam]
                                          · rcases h2bigk with h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c | h57c
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h0, h22, h26, h27, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              rcases p57_3 (m.d 0 2) (by simp) with h60 | h60
                                              · rcases p57_3 (m.d 1 2) (by simp) with h61 | h61
                                                · linarith only [h0, h61, hlam]
                                                · linarith only [h22, h61, hlam]
                                              · linarith only [h60, hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              rcases p57_3 (m.d 0 2) (by simp) with h65 | h65
                                              · rcases p57_3 (m.d 1 2) (by simp) with h66 | h66
                                                · linarith only [h0, h66, hlam]
                                                · linarith only [h23, h66, hlam]
                                              · linarith only [h65, hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              rcases p57_3 (m.d 0 2) (by simp) with h70 | h70
                                              · rcases p57_3 (m.d 1 2) (by simp) with h71 | h71
                                                · linarith only [h0, h71, hlam]
                                                · linarith only [h22, h26, h71, hlam]
                                              · linarith only [h70, hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h0, hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h0, h26, h27, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p57_1]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              rcases p57_3 (m.d 0 2) (by simp) with h78 | h78
                                              · rcases p57_3 (m.d 1 2) (by simp) with h79 | h79
                                                · rcases p57_3 (m.d 2 3) (by simp) with h80 | h80
                                                  · linarith only [h22, h80, hlam]
                                                  · linarith only [h25, h80, hlam]
                                                · linarith only [h79, hlam, p57_0]
                                              · linarith only [h4, h78, hlam]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              rcases p57_3 (m.d 0 2) (by simp) with h85 | h85
                                              · rcases p57_3 (m.d 1 2) (by simp) with h86 | h86
                                                · rcases p57_3 (m.d 2 3) (by simp) with h87 | h87
                                                  · linarith only [h22, h87, hlam]
                                                  · linarith only [h26, h87, hlam]
                                                · linarith only [h86, hlam, p57_0]
                                              · linarith only [h5, h85, hlam]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h3, hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h22, hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p57_1, u3elo2]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p57_1, u3elo2]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h4, hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h23, hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h25, hlam, p57_1]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h2, h23, h26, h27, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p57_1, u3elo0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h5, hlam, p57_0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h5, h7, hc12, hlam, hphi, ht23, p57_1, u3elo0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h26, hlam, p57_1]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [h1, h22, h26, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p57_1, u3elo0]
                                            · have p57_0 := h57c.1
                                              have p57_1 := h57c.2.1
                                              have p57_2 := h57c.2.2.1
                                              have p57_3 := h57c.2.2.2
                                              linarith only [hlam, p57_0]
                                    · linarith only [h3, h50, hlam]
                                  · linarith only [h1, h49, hlam]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 1) (by simp) with h109 | h109
                                  · rcases p29_3 (m.d 0 2) (by simp) with h110 | h110
                                    · rcases p29_3 (m.d 0 3) (by simp) with h111 | h111
                                      · linarith only [h111, h3, hlam]
                                      · linarith only [h111, h6, hlam]
                                    · linarith only [h110, h4, hlam]
                                  · linarith only [h109, h2, hlam]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  rcases p29_3 (m.d 0 1) (by simp) with h116 | h116
                                  · rcases p29_3 (m.d 0 2) (by simp) with h117 | h117
                                    · rcases p29_3 (m.d 0 3) (by simp) with h118 | h118
                                      · linarith only [h118, h3, hlam]
                                      · linarith only [h118, h7, hlam]
                                    · linarith only [h117, h5, hlam]
                                  · linarith only [h0, h116, h7, hc12, hlam, hphi, ht23, u3elo0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h1, hlam, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h3, hlam, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p29_1, u3elo0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p29_1, u3elo0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h2, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h4, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h6, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h8, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h0, h22, h26, h27, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h5, hlam, p29_1]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h7, hlam, p29_0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [h2, h23, h25, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p29_1, u3elo0]
                                · have p29_0 := h29c.1
                                  have p29_1 := h29c.2.1
                                  have p29_2 := h29c.2.2.1
                                  have p29_3 := h29c.2.2.2
                                  linarith only [hlam, p29_0]
                            · linarith only [h26, hc23, hlam, hphi, u3elo4]
                          · linarith only [h25, hc23, hlam, hphi, u3elo3]
                        · linarith only [h24, h6, hc13, hlam, hphi, u3elo0]
                      · linarith only [h22, h23, h4, h7, h8, hc23, hlam, hphi, u3elo0]
                    · linarith only [h22, hc12, hlam, hphi, ht23, u3elo2]
                · linarith only [h7, hc03, hlam, hphi, u3elo4]
              · linarith only [h1, h6, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h145 | h145
              · rcases m.htr 0 3 5 (by decide) (by decide) with h146 | h146
                · linarith only [h146, h3, h5, hc23, hlam, hphi, u3elo0]
                · linarith only [h146, hc03, hlam, hphi, u3elo4]
              · linarith only [h1, h145, hc13, hlam, hphi, u3elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h150 | h150
            · rcases m.htr 0 3 4 (by decide) (by decide) with h151 | h151
              · linarith only [h151, h3, h4, hc23, hlam, hphi, u3elo0]
              · linarith only [h151, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h154 | h154
              · linarith only [h154, h3, h4, hc23, hlam, hphi, u3elo0]
              · linarith only [h154, hc03, hlam, hphi, u3elo3]
        · linarith only [h3, hc02, hlam, hphi, ht23, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h158 | h158
        · rcases m.htr 0 2 4 (by decide) (by decide) with h159 | h159
          · linarith only [h0, h159, h2, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h161 | h161
            · rcases m.htr 0 3 4 (by decide) (by decide) with h162 | h162
              · linarith only [h0, h162, h2, hc12, hlam, hphi, ht23, u3elo0]
              · linarith only [h162, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h165 | h165
              · linarith only [h0, h165, h2, hc12, hlam, hphi, ht23, u3elo0]
              · linarith only [h165, hc03, hlam, hphi, u3elo3]
        · linarith only [h158, hc02, hlam, hphi, ht23, u3elo2]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h170 | h170
    · rcases m.htr 0 1 4 (by decide) (by decide) with h171 | h171
      · rcases m.htr 0 2 3 (by decide) (by decide) with h172 | h172
        · rcases m.htr 0 2 4 (by decide) (by decide) with h173 | h173
          · rcases m.htr 0 2 5 (by decide) (by decide) with h174 | h174
            · rcases m.htr 0 3 4 (by decide) (by decide) with h175 | h175
              · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
                · rcases m.htr 0 4 5 (by decide) (by decide) with h177 | h177
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h179 | h179
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h182 | h182
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h183 | h183
                              · linarith only [h0, h170, h178, h181, h183, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h175, h177, h183, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · linarith only [h182, hc23, hlam, hphi, u3elo4]
                          · linarith only [h181, hc23, hlam, hphi, u3elo3]
                        · linarith only [h175, h180, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h170, h173, h178, h179, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h178, hc02, hlam, hphi, ht23, u3elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h192 | h192
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h193 | h193
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h195 | h195
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
                              · linarith only [h170, h177, h191, h194, h196, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                              · rcases h0bigk with h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c | h198c
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h0, hlam, p198_1]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h0, h175, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p198_1]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  rcases p198_3 (m.d 0 1) (by simp) with h202 | h202
                                  · rcases p198_3 (m.d 0 2) (by simp) with h203 | h203
                                    · rcases p198_3 (m.d 0 3) (by simp) with h204 | h204
                                      · linarith only [h170, h204, hlam]
                                      · linarith only [h175, h204, hlam]
                                    · linarith only [h173, h203, hlam]
                                  · linarith only [h171, h202, hlam]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  rcases p198_3 (m.d 0 1) (by simp) with h209 | h209
                                  · rcases p198_3 (m.d 0 2) (by simp) with h210 | h210
                                    · rcases p198_3 (m.d 0 3) (by simp) with h211 | h211
                                      · linarith only [h170, h211, hlam]
                                      · linarith only [h176, h211, hlam]
                                    · linarith only [h174, h210, hlam]
                                  · linarith only [h209, hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h0, h170, h191, h195, h196, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p198_1]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  rcases p198_3 (m.d 0 1) (by simp) with h218 | h218
                                  · linarith only [h0, h218, hlam]
                                  · linarith only [h170, h218, hlam]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  rcases p198_3 (m.d 0 1) (by simp) with h221 | h221
                                  · linarith only [h0, h221, hlam]
                                  · linarith only [h171, h221, hlam]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  rcases p198_3 (m.d 0 1) (by simp) with h224 | h224
                                  · linarith only [h0, h224, hlam]
                                  · linarith only [h170, h191, h195, h196, h224, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p198_1]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h170, hlam, p198_1]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h172, hlam, p198_1]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h171, h192, h194, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p198_1, u3elo0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p198_1, u3elo0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h171, hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h173, hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h175, hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h177, hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h170, h191, h195, h196, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p198_1]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h174, hlam, p198_1]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h176, hlam, p198_0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [h171, h176, h192, h194, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p198_1, u3elo0]
                                · have p198_0 := h198c.1
                                  have p198_1 := h198c.2.1
                                  have p198_2 := h198c.2.2.1
                                  have p198_3 := h198c.2.2.2
                                  linarith only [hlam, p198_0]
                            · linarith only [h195, hc23, hlam, hphi, u3elo4]
                          · linarith only [h194, hc23, hlam, hphi, u3elo3]
                        · linarith only [h175, h193, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h173, h192, hlam]
                    · linarith only [h0, h191, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h176, hc03, hlam, hphi, u3elo4]
              · linarith only [h170, h175, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h249 | h249
              · rcases m.htr 0 3 5 (by decide) (by decide) with h250 | h250
                · linarith only [h0, h170, h174, h250, hc13, hlam, hphi, u3elo0]
                · linarith only [h250, hc03, hlam, hphi, u3elo4]
              · linarith only [h170, h249, hc13, hlam, hphi, u3elo3]
          · linarith only [h0, h171, h173, hlam]
        · linarith only [h0, h170, h172, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h256 | h256
        · rcases m.htr 0 2 4 (by decide) (by decide) with h257 | h257
          · rcases m.htr 0 2 5 (by decide) (by decide) with h258 | h258
            · rcases m.htr 0 3 4 (by decide) (by decide) with h259 | h259
              · linarith only [h170, h171, h259, hc13, hlam, hphi, u3elo0]
              · linarith only [h259, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h262 | h262
              · linarith only [h170, h171, h262, hc13, hlam, hphi, u3elo0]
              · linarith only [h262, hc03, hlam, hphi, u3elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h265 | h265
            · rcases m.htr 0 3 4 (by decide) (by decide) with h266 | h266
              · linarith only [h256, h257, h266, hc23, hlam, hphi, u3elo0]
              · linarith only [h266, hc03, hlam, hphi, u3elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h269 | h269
              · linarith only [h0, h170, h257, h269, hc13, hlam, hphi, u3elo0]
              · linarith only [h269, hc03, hlam, hphi, u3elo3]
        · linarith only [h0, h170, h256, hc13, hlam, hphi, u3elo2]
    · linarith only [h170, hc01, hlam, hphi, ht12, ht23, u3elo1]

end R2N4
