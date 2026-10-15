import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_13_24_L_0_M_IR (m : N7Model)
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h3elo := hb3.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · linarith only [h11, h3, h8, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
                        · linarith only [h1, h11, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi3]
                      · linarith only [h1, h10, h2, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi2]
                    · linarith only [h8, h9, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                  · linarith only [h1, h8, hc23, hlam, hphi, u3elo0]
                · linarith only [h1, h2, h7, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
              · linarith only [h1, h6, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h19 | h19
              · rcases m.htr 1 4 5 (by decide) (by decide) with h20 | h20
                · linarith only [h19, h20, h3, h5, hlam]
                · linarith only [h1, h2, h20, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
              · linarith only [h1, h19, hc13, hlam, hphi, u3elo0]
          · linarith only [h0, h1, h3, h4, hc23, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
          · linarith only [h25, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
            · rcases m.htr 1 3 4 (by decide) (by decide) with h28 | h28
              · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                · rcases m.htr 2 3 4 (by decide) (by decide) with h30 | h30
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h31 | h31
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h32 | h32
                      · linarith only [h0, h1, h25, h27, h32, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                      · linarith only [h25, h27, h28, h29, h32, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h27, h29, h3, h31, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi4]
                  · linarith only [h27, h29, h3, h30, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                · linarith only [h1, h2, h29, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
              · linarith only [h1, h28, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h39 | h39
              · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h42 | h42
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                        · linarith only [h1, h44, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                        · linarith only [h1, h2, h44, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi3]
                      · linarith only [h25, h40, h43, hlam]
                    · linarith only [h3, h42, hc12, hlam, hphi, ht23, u3elo4]
                  · linarith only [h3, h39, h40, h41, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                · linarith only [h1, h2, h40, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
              · linarith only [h1, h39, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
        · rcases m.htr 1 2 4 (by decide) (by decide) with h53 | h53
          · rcases m.htr 1 2 5 (by decide) (by decide) with h54 | h54
            · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
              · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                · linarith only [h2, h55, h56, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h60 | h60
                      · linarith only [h0, h2, h60, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                        · linarith only [h2, h52, h58, h62, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · rcases h4bigk with h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c | h64c
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h2, h53, h58, hc45, hlam, hphi, p64_1, u4ehi3]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h2, h58, hc45, hlam, hphi, p64_1, u4ehi3]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, p64_1, u4ehi3]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h2, hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h0, h55, h58, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p64_1, u3elo1, u4ehi3]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h55, h58, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p64_1, u3elo1, u4ehi3]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h55, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p64_1, u3elo1, u4ehi3]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h56, hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h0, hlam, p64_1]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h53, hlam, p64_1]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h0, hc02, hlam, hphi, ht0b, ht45, ht5b, p64_1, u4ehi3]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h60, hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h1, hlam, p64_1]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h55, hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h58, hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h62, hlam, p64_0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [hc45, hlam, hphi, p64_1, u4ehi0]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [hc45, hlam, hphi, p64_1, u4ehi1]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [h58, hc45, hlam, hphi, p64_1, u4ehi3]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [hc45, hlam, hphi, p64_1, u4ehi3]
                          · have p64_0 := h64c.1
                            have p64_1 := h64c.2.1
                            have p64_2 := h64c.2.2.1
                            have p64_3 := h64c.2.2.2
                            linarith only [hlam, p64_0]
                    · linarith only [h58, h59, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                  · linarith only [h1, h58, hc23, hlam, hphi, u3elo0]
              · linarith only [h1, h55, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h93 | h93
              · rcases m.htr 1 4 5 (by decide) (by decide) with h94 | h94
                · linarith only [h2, h53, h54, h94, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                  · linarith only [h52, h54, h94, h96, hc45, hlam, hphi, u4ehi3]
                  · linarith only [h93, h96, hc23, hlam, hphi, u3elo1]
              · linarith only [h1, h93, hc13, hlam, hphi, u3elo0]
          · linarith only [h0, h1, h52, h53, hc23, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
          · linarith only [h101, h52, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
            · rcases m.htr 1 3 4 (by decide) (by decide) with h104 | h104
              · rcases m.htr 1 4 5 (by decide) (by decide) with h105 | h105
                · linarith only [h0, h101, h105, h2, hlam]
                · linarith only [h0, h101, h103, h105, h2, hc45, hlam, hphi, u4ehi1]
              · linarith only [h1, h104, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h109 | h109
              · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                · linarith only [h0, h101, h110, h2, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h112 | h112
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h113 | h113
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h114 | h114
                      · linarith only [h0, h114, h2, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h116 | h116
                        · linarith only [h109, h116, h2, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · rcases h4bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h109, h2, hc45, hlam, hphi, p118_1, u4ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h101, h109, h2, h52, hc12, hc45, hlam, hphi, ht23, p118_1, u3elo2, u4ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h2, hc45, hlam, hphi, p118_1, u4ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h2, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h0, h101, hlam, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h101, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h0, h101, hc02, hlam, hphi, ht0b, ht45, ht5b, p118_1, u4ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h110, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h0, hlam, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h0, hc02, hlam, hphi, ht0b, ht45, ht5b, p118_1, u4ehi1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h0, h2, hc45, hlam, hphi, p118_1, u4ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h114, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h1, hlam, p118_1]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h109, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h112, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h116, hlam, p118_0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hc45, hlam, hphi, p118_1, u4ehi0]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h109, hc45, hlam, hphi, p118_1, u4ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [h101, h109, h52, hc12, hc45, hlam, hphi, ht23, p118_1, u3elo2, u4ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hc45, hlam, hphi, p118_1, u4ehi3]
                          · have p118_0 := h118c.1
                            have p118_1 := h118c.2.1
                            have p118_2 := h118c.2.2.1
                            have p118_3 := h118c.2.2.2
                            linarith only [hlam, p118_0]
                    · linarith only [h109, h113, h52, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                  · linarith only [h109, h112, h52, hlam]
              · linarith only [h1, h109, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h147 | h147
      · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
        · rcases m.htr 1 2 4 (by decide) (by decide) with h149 | h149
          · rcases m.htr 1 2 5 (by decide) (by decide) with h150 | h150
            · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
              · linarith only [h1, h151, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h153 | h153
                · rcases m.htr 2 3 4 (by decide) (by decide) with h154 | h154
                  · linarith only [h151, h154, hc13, hlam, hphi, u3elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h157 | h157
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h158 | h158
                        · linarith only [h148, h151, h156, h158, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                        · linarith only [h149, h151, h157, h158, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1, h147, h157, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h162 | h162
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h163 | h163
                        · rcases h4bigk with h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p164_1, u3elo3, u4ehi1]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h1, h162, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p164_1, u3elo3, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h1, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h1, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p164_1, u3elo3, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h0, h162, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p164_1, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h149, h162, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p164_1, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h151, hlam, p164_1]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h151, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p164_1, u3elo3, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h0, hlam, p164_1]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h149, hlam, p164_1]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h154, hlam, p164_1]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h0, hc02, hlam, hphi, ht0b, ht45, ht5b, p164_1, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p164_1, u3elo3, u4ehi0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p164_1, u3elo3, u4ehi1]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p164_1, u3elo3, u4ehi2]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p164_1, u3elo3, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h147, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h153, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h162, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h163, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                        · linarith only [h0, h162, h163, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h1, h147, h162, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                · linarith only [h1, h147, h153, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h193 | h193
              · linarith only [h1, h147, h193, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h195 | h195
                · linarith only [h149, h150, h195, hlam]
                · linarith only [h1, h147, h195, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
          · linarith only [h0, h1, h148, h149, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
          · linarith only [h148, h199, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h201 | h201
            · rcases m.htr 1 3 4 (by decide) (by decide) with h202 | h202
              · linarith only [h0, h1, h199, h202, hc12, hlam, hphi, ht23, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h204 | h204
                · rcases m.htr 2 3 4 (by decide) (by decide) with h205 | h205
                  · linarith only [h202, h205, hc13, hlam, hphi, u3elo2]
                  · linarith only [h148, h201, h204, h205, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                · linarith only [h1, h147, h204, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h209 | h209
              · linarith only [h1, h147, h209, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h211 | h211
                · rcases m.htr 2 3 4 (by decide) (by decide) with h212 | h212
                  · linarith only [h209, h212, hc13, hlam, hphi, u3elo2]
                  · linarith only [h148, h212, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h1, h147, h211, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h216 | h216
        · rcases m.htr 1 2 4 (by decide) (by decide) with h217 | h217
          · rcases m.htr 1 2 5 (by decide) (by decide) with h218 | h218
            · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
              · linarith only [h1, h219, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h221 | h221
                · linarith only [h147, h219, h221, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
                  · linarith only [h216, h219, h223, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h225 | h225
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h226 | h226
                      · linarith only [h0, h221, h226, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                      · linarith only [h223, h225, h226, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h229 | h229
                      · linarith only [h147, h217, h229, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h231 | h231
                        · linarith only [h219, h221, h231, hc13, hlam, hphi, u3elo3]
                        · rcases h4bigk with h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c | h233c
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [hlam, p233_0]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h1, h217, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p233_1, u3elo3, u4ehi2]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h1, h231, hc45, hlam, hphi, p233_1, u4ehi2]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h1, hlam, p233_0]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h147, hlam, p233_0]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h0, h219, h231, hc45, hlam, hphi, p233_1, u4ehi2]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [hlam, p233_0]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h219, h231, hc45, hlam, hphi, p233_1, u4ehi2]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h219, hlam, p233_1]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h221, hlam, p233_0]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h0, hlam, p233_1]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h217, hlam, p233_1]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [hlam, p233_0]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h223, hlam, p233_1]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h229, hlam, p233_0]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h0, h231, hc45, hlam, hphi, p233_1, u4ehi2]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h231, hc45, hlam, hphi, p233_1, u4ehi1]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h231, hc45, hlam, hphi, p233_1, u4ehi2]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [hlam, p233_0]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h231, hlam, p233_0]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h0, hc45, hlam, hphi, p233_1, u4ehi2]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h217, hc45, hlam, hphi, p233_1, u4ehi2]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [hc45, hlam, hphi, p233_1, u4ehi2]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [h1, hc03, hc45, hlam, hphi, ht34, p233_1]
                          · have p233_0 := h233c.1
                            have p233_1 := h233c.2.1
                            have p233_2 := h233c.2.2.1
                            have p233_3 := h233c.2.2.2
                            linarith only [hlam, p233_0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
              · linarith only [h1, h259, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h261 | h261
                · linarith only [h0, h147, h217, h218, h261, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h263 | h263
                  · linarith only [h1, h263, hc03, hlam, hphi, u3elo2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h265 | h265
                    · linarith only [h216, h217, h218, h259, h265, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi2]
                    · linarith only [h217, h218, h265, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi2]
          · linarith only [h0, h147, h216, h217, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
          · linarith only [h216, h269, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
            · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
              · linarith only [h0, h1, h269, h271, h272, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                · linarith only [h0, h147, h269, h271, h274, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h0, h147, h269, h271, h274, hc45, hlam, hphi, u4ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
              · linarith only [h1, h277, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h279 | h279
                · linarith only [h0, h147, h269, h279, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                  · linarith only [h1, h281, hc03, hlam, hphi, u3elo2]
                  · linarith only [h216, h281, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h284 | h284
    · rcases m.htr 0 4 5 (by decide) (by decide) with h285 | h285
      · rcases m.htr 1 2 3 (by decide) (by decide) with h286 | h286
        · rcases m.htr 1 2 4 (by decide) (by decide) with h287 | h287
          · rcases m.htr 1 2 5 (by decide) (by decide) with h288 | h288
            · rcases m.htr 1 3 4 (by decide) (by decide) with h289 | h289
              · rcases m.htr 1 4 5 (by decide) (by decide) with h290 | h290
                · rcases m.htr 2 3 4 (by decide) (by decide) with h291 | h291
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h292 | h292
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h293 | h293
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h294 | h294
                        · linarith only [h284, h294, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                        · linarith only [h0, h285, h286, h291, h294, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h285, h293, hlam]
                    · linarith only [h0, h291, h292, hc02, hlam, hphi, ht23, u3elo4]
                  · linarith only [h284, h291, hc23, hlam, hphi, u3elo0]
                · linarith only [h0, h285, h287, h290, hlam]
              · linarith only [h284, h289, hc13, hlam, hphi, u3elo0]
            · linarith only [h0, h285, h287, h288, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h303 | h303
            · rcases m.htr 1 3 4 (by decide) (by decide) with h304 | h304
              · linarith only [h286, h287, h304, hlam]
              · linarith only [h284, h304, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h307 | h307
              · linarith only [h286, h287, h307, hlam]
              · linarith only [h284, h307, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h310 | h310
          · linarith only [h286, h310, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h312 | h312
            · rcases m.htr 1 3 4 (by decide) (by decide) with h313 | h313
              · rcases m.htr 1 4 5 (by decide) (by decide) with h314 | h314
                · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h316 | h316
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h317 | h317
                      · linarith only [h310, h312, h315, h317, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                      · linarith only [h284, h285, h310, h312, h317, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h286, h312, h314, h316, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi4]
                  · linarith only [h286, h312, h314, h315, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                · linarith only [h284, h285, h314, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
              · linarith only [h284, h313, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h324 | h324
              · rcases m.htr 1 4 5 (by decide) (by decide) with h325 | h325
                · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h327 | h327
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h328 | h328
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h329 | h329
                        · linarith only [h284, h329, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi4]
                        · linarith only [h0, h285, h326, h329, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi3]
                      · linarith only [h0, h285, h328, hlam]
                    · linarith only [h0, h285, h326, h327, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi4]
                  · linarith only [h286, h324, h325, h326, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                · linarith only [h284, h285, h325, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0, u4ehi1]
              · linarith only [h284, h324, hc13, hlam, hphi, u3elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
        · rcases m.htr 1 2 4 (by decide) (by decide) with h338 | h338
          · rcases m.htr 1 2 5 (by decide) (by decide) with h339 | h339
            · rcases m.htr 1 3 4 (by decide) (by decide) with h340 | h340
              · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
                · linarith only [h285, h340, h341, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h343 | h343
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h344 | h344
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h345 | h345
                      · linarith only [h338, h341, h345, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h347 | h347
                        · linarith only [h337, h341, h343, h347, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi1]
                        · rcases h4bigk with h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c | h349c
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h0, h338, hlam, p349_1]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h0, hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h0, h338, h341, hc45, hlam, hphi, p349_1, u4ehi3]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h285, hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h341, hc45, hlam, hphi, p349_1, u4ehi0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h341, hc45, hlam, hphi, p349_1, u4ehi2]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h341, hc45, hlam, hphi, p349_1, u4ehi3]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h341, hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h284, h338, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p349_1, u4ehi3]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h338, hlam, p349_1]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h338, h341, hc45, hlam, hphi, p349_1, u4ehi3]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h345, hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h284, hlam, p349_1]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h340, hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h343, hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h347, hlam, p349_0]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h284, hc45, hlam, hphi, p349_1, u4ehi3]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [hc45, hlam, hphi, p349_1, u4ehi1]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [h0, hc02, hc45, hlam, hphi, ht23, ht34, p349_1]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [hc45, hlam, hphi, p349_1, u4ehi3]
                          · have p349_0 := h349c.1
                            have p349_1 := h349c.2.1
                            have p349_2 := h349c.2.2.1
                            have p349_3 := h349c.2.2.2
                            linarith only [hlam, p349_0]
                    · linarith only [h343, h344, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                  · linarith only [h284, h343, hc23, hlam, hphi, u3elo0]
              · linarith only [h284, h340, hc13, hlam, hphi, u3elo0]
            · linarith only [h0, h338, h339, hc02, hc25, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h379 | h379
            · rcases m.htr 1 3 4 (by decide) (by decide) with h380 | h380
              · linarith only [h337, h338, h380, hlam]
              · linarith only [h284, h380, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h383 | h383
              · linarith only [h337, h338, h383, hlam]
              · linarith only [h284, h383, hc13, hlam, hphi, u3elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
          · linarith only [h0, h337, h386, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi0]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h388 | h388
            · rcases m.htr 1 3 4 (by decide) (by decide) with h389 | h389
              · rcases m.htr 1 4 5 (by decide) (by decide) with h390 | h390
                · linarith only [h284, h285, h389, h390, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi3]
                · linarith only [h386, h388, h390, hlam]
              · linarith only [h284, h389, hc13, hlam, hphi, u3elo0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h394 | h394
              · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                · linarith only [h284, h285, h394, h395, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi3]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h397 | h397
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h398 | h398
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h399 | h399
                      · linarith only [h395, h397, h399, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h401 | h401
                        · linarith only [h337, h386, h394, h399, h401, hc12, hlam, hphi, ht23, u3elo2]
                        · rcases h4bigk with h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h0, h394, h399, hc45, hlam, hphi, p403_1, u4ehi3]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h0, hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h0, h399, hc45, hlam, hphi, p403_1, u4ehi3]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h285, hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h284, h386, h399, hc45, hlam, hphi, p403_1, u4ehi3]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h386, hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h386, h399, hc45, hlam, hphi, p403_1, u4ehi3]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h395, hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h284, h399, hc45, hlam, hphi, p403_1, u4ehi3]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h399, hc45, hlam, hphi, p403_1, u4ehi1]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h399, hc45, hlam, hphi, p403_1, u4ehi3]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h399, hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h284, hlam, p403_1]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h394, hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h397, hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h401, hlam, p403_0]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h284, hc45, hlam, hphi, p403_1, u4ehi3]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [h394, hc45, hlam, hphi, p403_1, u4ehi3]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [hc45, hlam, hphi, p403_1, u4ehi2]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [hc45, hlam, hphi, p403_1, u4ehi3]
                          · have p403_0 := h403c.1
                            have p403_1 := h403c.2.1
                            have p403_2 := h403c.2.2.1
                            have p403_3 := h403c.2.2.2
                            linarith only [hlam, p403_0]
                    · linarith only [h337, h394, h398, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4, u4ehi3]
                  · linarith only [h337, h394, h397, hlam]
              · linarith only [h284, h394, hc13, hlam, hphi, u3elo0]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h432 | h432
      · rcases m.htr 1 2 3 (by decide) (by decide) with h433 | h433
        · rcases m.htr 1 2 4 (by decide) (by decide) with h434 | h434
          · rcases m.htr 1 2 5 (by decide) (by decide) with h435 | h435
            · rcases m.htr 1 3 4 (by decide) (by decide) with h436 | h436
              · linarith only [h284, h432, h436, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h438 | h438
                · rcases m.htr 2 3 4 (by decide) (by decide) with h439 | h439
                  · linarith only [h0, h432, h434, h436, h439, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi4]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h441 | h441
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h442 | h442
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h443 | h443
                        · linarith only [h433, h436, h441, h443, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                        · linarith only [h0, h284, h432, h434, h443, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h432, h442, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h447 | h447
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h448 | h448
                        · rcases h4bigk with h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h0, h434, hlam, p449_1]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h0, hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h284, hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h0, h434, h436, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p449_1, u3elo3, u4ehi4]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h436, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p449_1, u3elo3, u4ehi0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h436, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p449_1, u3elo3, u4ehi2]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h436, hlam, p449_1]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h436, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p449_1, u3elo3, u4ehi4]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h432, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p449_1, u4ehi4]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h434, hlam, p449_1]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h439, hlam, p449_1]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h434, h436, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p449_1, u3elo3, u4ehi4]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h432, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p449_1, u3elo3, u4ehi4]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p449_1, u3elo3, u4ehi1]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h0, h432, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p449_1, u3elo3, u4ehi4]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p449_1, u3elo3, u4ehi4]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h432, hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h438, hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h447, hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [h448, hlam, p449_0]
                          · have p449_0 := h449c.1
                            have p449_1 := h449c.2.1
                            have p449_2 := h449c.2.2.1
                            have p449_3 := h449c.2.2.2
                            linarith only [hlam, p449_0]
                        · linarith only [h284, h432, h448, hlam]
                      · linarith only [h0, h432, h447, hlam]
                · linarith only [h0, h432, h434, h438, hlam]
            · linarith only [h0, h432, h434, h435, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
            · rcases m.htr 1 3 4 (by decide) (by decide) with h480 | h480
              · linarith only [h284, h480, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h482 | h482
                · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                  · linarith only [h433, h434, h480, h483, hlam]
                  · linarith only [h433, h434, h483, hc23, hlam, hphi, u3elo3]
                · linarith only [h284, h432, h482, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h487 | h487
              · linarith only [h284, h432, h487, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                  · linarith only [h433, h479, h487, h490, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h433, h434, h490, hc23, hlam, hphi, u3elo3]
                · linarith only [h284, h432, h489, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h494 | h494
          · linarith only [h433, h494, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h496 | h496
            · rcases m.htr 1 3 4 (by decide) (by decide) with h497 | h497
              · linarith only [h284, h432, h497, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h499 | h499
                · rcases m.htr 2 3 4 (by decide) (by decide) with h500 | h500
                  · linarith only [h433, h497, h500, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h433, h496, h499, h500, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi4]
                · linarith only [h284, h432, h499, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h504 | h504
              · linarith only [h284, h432, h504, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1, u4ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h506 | h506
                · rcases m.htr 2 3 4 (by decide) (by decide) with h507 | h507
                  · linarith only [h284, h507, hc03, hlam, hphi, u3elo2]
                  · linarith only [h433, h507, hc12, hlam, hphi, ht23, u3elo3]
                · linarith only [h284, h432, h506, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
        · rcases m.htr 1 2 4 (by decide) (by decide) with h512 | h512
          · rcases m.htr 1 2 5 (by decide) (by decide) with h513 | h513
            · rcases m.htr 1 3 4 (by decide) (by decide) with h514 | h514
              · linarith only [h284, h514, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h516 | h516
                · linarith only [h432, h514, h516, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h518 | h518
                  · linarith only [h284, h511, h518, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h520 | h520
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h521 | h521
                      · linarith only [h432, h512, h521, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                      · linarith only [h0, h511, h514, h520, h521, hc02, hlam, hphi, ht23, u3elo3]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h524 | h524
                      · linarith only [h512, h516, h524, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h526 | h526
                        · linarith only [h0, h512, h516, h526, hc02, hlam, hphi, ht23, u3elo3]
                        · rcases h4bigk with h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h0, h512, hlam, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h0, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h284, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h432, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h514, h526, hc45, hlam, hphi, p528_1, u4ehi0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h0, h514, h526, hc02, hc45, hlam, hphi, ht23, ht34, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h514, hlam, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h516, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h512, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p528_1, u4ehi0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h512, hlam, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h518, hlam, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h524, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h526, hc45, hlam, hphi, p528_1, u4ehi0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h526, hc45, hlam, hphi, p528_1, u4ehi1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h526, hc45, hlam, hphi, p528_1, u4ehi2]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h526, hlam, p528_0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hc45, hlam, hphi, p528_1, u4ehi0]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hc45, hlam, hphi, p528_1, u4ehi1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h0, hc02, hc45, hlam, hphi, ht23, ht34, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [h514, hc13, hc45, hlam, hphi, ht34, p528_1]
                          · have p528_0 := h528c.1
                            have p528_1 := h528c.2.1
                            have p528_2 := h528c.2.2.1
                            have p528_3 := h528c.2.2.2
                            linarith only [hlam, p528_0]
            · linarith only [h0, h512, h513, hc02, hc25, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h555 | h555
            · rcases m.htr 1 3 4 (by decide) (by decide) with h556 | h556
              · linarith only [h284, h556, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h558 | h558
                · linarith only [h432, h556, h558, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                · linarith only [h512, h555, h558, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h561 | h561
              · linarith only [h284, h561, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h563 | h563
                · linarith only [h432, h561, h563, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h565 | h565
                  · linarith only [h561, h565, hc13, hlam, hphi, u3elo2]
                  · linarith only [h511, h512, h565, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h568 | h568
          · linarith only [h511, h568, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2, u4ehi2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h570 | h570
            · rcases m.htr 1 3 4 (by decide) (by decide) with h571 | h571
              · linarith only [h284, h571, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h573 | h573
                · linarith only [h432, h571, h573, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                · linarith only [h568, h570, h573, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h576 | h576
              · linarith only [h284, h576, hc03, hlam, hphi, u3elo1]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h578 | h578
                · linarith only [h432, h576, h578, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3, u4ehi0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h580 | h580
                  · linarith only [h511, h576, h580, hc12, hlam, hphi, ht23, u3elo2]
                  · linarith only [h511, h580, hc12, hlam, hphi, ht23, u3elo3]

theorem r1l7_20_11_13_14_H_L_L_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h3, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                · linarith only [h0, h10, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h10, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h13 | h13
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h14, h2, h3, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h17, h2, h3, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · linarith only [h3, h4, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h21 | h21
          · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
            · rcases m.htr 0 3 4 (by decide) (by decide) with h23 | h23
              · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                · linarith only [h0, h21, h24, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h26 | h26
                  · linarith only [h0, h26, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h21, h26, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h21, h23, h3, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h30 | h30
              · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                · linarith only [h0, h31, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h33 | h33
                  · linarith only [h0, h33, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h21, h33, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h21, h3, h30, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h37 | h37
            · rcases m.htr 0 3 4 (by decide) (by decide) with h38 | h38
              · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                · linarith only [h0, h39, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h41 | h41
                  · linarith only [h0, h21, h41, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h43 | h43
                    · linarith only [h1, h41, h43, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h37, h43, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                · linarith only [h0, h46, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h48 | h48
                  · linarith only [h0, h3, h37, h38, h48, hc24, hc25, hlam, hphi, ht0b, ht5b, u0elo0, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h50 | h50
                    · linarith only [h1, h48, h50, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h3, h37, h38, h50, hc12, hlam, hphi, ht23, ht34, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h53 | h53
              · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                · linarith only [h0, h3, h54, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h56 | h56
                  · linarith only [h0, h21, h56, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h58 | h58
                    · linarith only [h1, h37, h56, h58, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h60 | h60
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h61 | h61
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h62 | h62
                          · linarith only [h1, h62, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                              · linarith only [h62, h65, hc14, hlam, hphi, u4elo2]
                              · linarith only [h0, h21, h65, hc12, hlam, hphi, ht23, ht34, u4elo4]
                            · linarith only [h0, h3, h64, hc12, hlam, hphi, ht23, ht34, u4elo3]
                        · linarith only [h2, h60, h61, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h53, h60, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                · linarith only [h0, h21, h71, hc23, hlam, hphi, ht34, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
                  · linarith only [h0, h73, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h75 | h75
                    · linarith only [h1, h37, h73, h75, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h77 | h77
                      · linarith only [h53, h77, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                        · linarith only [h1, h77, h79, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                          · linarith only [h1, h81, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                            · linarith only [h0, h3, h53, h83, hc12, hlam, hphi, ht23, u3elo2]
                            · linarith only [h0, h3, h83, hc12, hlam, hphi, ht23, ht34, u4elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h86 | h86
        · rcases m.htr 0 2 4 (by decide) (by decide) with h87 | h87
          · rcases m.htr 0 2 5 (by decide) (by decide) with h88 | h88
            · linarith only [h0, h2, h88, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h90 | h90
              · rcases m.htr 1 2 3 (by decide) (by decide) with h91 | h91
                · linarith only [h0, h2, h91, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h2, h86, h91, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                · linarith only [h0, h2, h94, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · linarith only [h0, h2, h86, h94, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · linarith only [h86, h87, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h98 | h98
          · rcases m.htr 0 2 5 (by decide) (by decide) with h99 | h99
            · linarith only [h0, h2, h86, h99, hc12, hlam, hphi, ht23, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h101 | h101
              · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                · linarith only [h0, h102, h86, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                  · linarith only [h0, h104, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · linarith only [h104, h98, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h101, h86, h98, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h108 | h108
            · linarith only [h1, h108, h2, h98, hc14, hlam, hphi, u4elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h110 | h110
              · rcases m.htr 1 2 3 (by decide) (by decide) with h111 | h111
                · linarith only [h0, h111, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h113 | h113
                  · linarith only [h0, h113, h2, h98, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h115 | h115
                    · linarith only [h0, h108, h115, h2, h86, hc01, hlam, hphi, ht12, ht23, u3elo2]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                        · linarith only [h1, h113, h118, h2, hc12, hlam, hphi, ht23, u3elo1]
                        · linarith only [h1, h113, h118, h2, hc12, hlam, hphi, ht23, u3elo4]
                      · linarith only [h110, h117, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                · linarith only [h0, h122, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                  · linarith only [h0, h124, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                    · linarith only [h1, h124, h126, h2, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
                      · linarith only [h110, h128, h86, hc02, hlam, hphi, ht23, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h130 | h130
                        · linarith only [h1, h128, h130, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h1, h122, h128, h130, h2, hc12, hlam, hphi, ht23, u3elo4]
    · linarith only [h0, h1, hc12, hlam, hphi, ht23, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h134 | h134
    · rcases m.htr 0 1 5 (by decide) (by decide) with h135 | h135
      · rcases m.htr 0 2 3 (by decide) (by decide) with h136 | h136
        · rcases m.htr 0 2 4 (by decide) (by decide) with h137 | h137
          · rcases m.htr 0 2 5 (by decide) (by decide) with h138 | h138
            · rcases m.htr 0 3 4 (by decide) (by decide) with h139 | h139
              · rcases m.htr 1 2 3 (by decide) (by decide) with h140 | h140
                · rcases m.htr 1 2 4 (by decide) (by decide) with h141 | h141
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h142 | h142
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h144 | h144
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                          · linarith only [h134, h145, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                            · linarith only [h136, h147, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h139, h147, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h0, h135, h143, h144, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · linarith only [h136, h139, h143, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h138, h142, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h134, h141, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h134, h140, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                · rcases m.htr 1 2 4 (by decide) (by decide) with h156 | h156
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h157 | h157
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h158 | h158
                      · linarith only [h139, h158, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h160 | h160
                        · linarith only [h134, h158, h160, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                          · linarith only [h0, h134, h162, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h164 | h164
                            · linarith only [h136, h164, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h166 | h166
                              · linarith only [h158, h162, h166, hc13, hlam, hphi, ht34, u4elo2]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h168 | h168
                                · linarith only [h155, h158, h162, h168, hc23, hlam, hphi, u3elo3]
                                · linarith only [h136, h139, h168, hc23, hlam, hphi, ht34, u4elo4]
                    · linarith only [h0, h138, h157, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h134, h156, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h134, h136, h155, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · linarith only [h0, h135, h138, hlam]
          · linarith only [h0, h134, h137, hc14, hlam, hphi, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h176 | h176
          · rcases m.htr 0 2 5 (by decide) (by decide) with h177 | h177
            · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
              · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                · rcases m.htr 1 2 4 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h181 | h181
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h183 | h183
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h184 | h184
                          · linarith only [h0, h134, h136, h179, h184, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h187 | h187
                              · linarith only [h180, h184, h187, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h189 | h189
                                · linarith only [h180, h184, h186, h189, hlam]
                                · rcases h1bigk with h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c | h191c
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h0, hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h0, h136, h179, hlam, p191_1]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h0, h136, h179, h180, h186, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p191_1, u3elo1]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h0, h136, h179, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p191_1, u3elo1]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    rcases p191_3 (m.d 0 1) (by simp) with h197 | h197
                                    · linarith only [h197, hlam, p191_0]
                                    · rcases p191_3 (m.d 1 2) (by simp) with h199 | h199
                                      · rcases p191_3 (m.d 1 3) (by simp) with h200 | h200
                                        · linarith only [h179, h200, hlam]
                                        · linarith only [h0, h136, h179, h200, hlam]
                                      · linarith only [h199, hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h0, h136, h179, hc01, hc12, hlam, hphi, p191_1]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h0, h134, h136, h179, hlam, p191_2]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h0, h135, h136, h179, hlam, p191_2]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h135, h181, h186, h187, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p191_1, u3elo1]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h179, hlam, p191_1]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    rcases p191_3 (m.d 0 1) (by simp) with h211 | h211
                                    · linarith only [h0, h136, h179, h211, hlam]
                                    · linarith only [h134, h211, hlam]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    rcases p191_3 (m.d 0 1) (by simp) with h214 | h214
                                    · linarith only [h0, h136, h179, h214, hlam]
                                    · linarith only [h135, h214, hlam]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h134, hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h180, hlam, p191_1]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h182, hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h184, hlam, p191_1]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h135, hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h181, hlam, p191_1]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h183, hlam, p191_0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [h135, hc14, hlam, hphi, ht0b, ht45, ht5b, p191_1, u0elo0]
                                  · have p191_0 := h191c.1
                                    have p191_1 := h191c.2.1
                                    have p191_2 := h191c.2.2.1
                                    have p191_3 := h191c.2.2.2
                                    linarith only [hlam, p191_0]
                            · linarith only [h0, h136, h186, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · linarith only [h0, h136, h179, h183, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h134, h136, h179, h180, h182, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h134, h136, h179, h180, h181, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h136, h179, h180, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h134, h179, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h0, h134, h136, h178, hc14, hlam, hphi, u4elo3]
            · linarith only [h0, h135, h177, hlam]
          · linarith only [h0, h134, h176, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h236 | h236
        · rcases m.htr 0 2 4 (by decide) (by decide) with h237 | h237
          · rcases m.htr 0 2 5 (by decide) (by decide) with h238 | h238
            · rcases m.htr 0 3 4 (by decide) (by decide) with h239 | h239
              · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
                · rcases m.htr 1 2 4 (by decide) (by decide) with h241 | h241
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h242 | h242
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h243 | h243
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h244 | h244
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h245 | h245
                          · linarith only [h134, h245, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h134, h135, h245, hc14, hlam, hphi, u4elo4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h248 | h248
                          · linarith only [h134, h248, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h134, h135, h241, h248, hc24, hlam, hphi, u4elo4]
                      · linarith only [h239, h243, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h238, h242, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h134, h241, hc14, hlam, hphi, u4elo2]
                · linarith only [h0, h134, h240, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h255 | h255
                · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h257 | h257
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h258 | h258
                      · linarith only [h239, h258, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h260 | h260
                        · linarith only [h134, h258, h260, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h134, h135, h258, h260, hc13, hlam, hphi, u3elo4]
                    · linarith only [h238, h257, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h256, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h134, h236, h255, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h266 | h266
              · rcases m.htr 1 2 3 (by decide) (by decide) with h267 | h267
                · rcases m.htr 1 2 4 (by decide) (by decide) with h268 | h268
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h269 | h269
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h270 | h270
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h271 | h271
                        · linarith only [h236, h238, h269, h271, hc23, hlam, hphi, u3elo1]
                        · linarith only [h236, h238, h269, h271, hc23, hlam, hphi, u3elo4]
                      · linarith only [h236, h266, h270, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
                        · linarith only [h267, h269, h276, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h278 | h278
                          · linarith only [h134, h278, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h134, h269, h278, hc14, hlam, hphi, u4elo4]
                      · linarith only [h236, h238, h266, h275, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                  · linarith only [h0, h268, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h134, h236, h238, h267, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h284 | h284
                · rcases m.htr 1 2 4 (by decide) (by decide) with h285 | h285
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h286 | h286
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h287 | h287
                      · linarith only [h266, h287, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
                        · linarith only [h134, h287, h289, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h134, h238, h286, h287, h289, hc13, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h292 | h292
                      · linarith only [h236, h266, h292, hc23, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h294 | h294
                        · linarith only [h134, h292, h294, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h134, h284, h286, h292, h294, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h285, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h134, h236, h238, h284, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
          · linarith only [h236, h237, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h300 | h300
          · rcases m.htr 0 2 5 (by decide) (by decide) with h301 | h301
            · rcases m.htr 0 3 4 (by decide) (by decide) with h302 | h302
              · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
                · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                          · linarith only [h134, h135, h236, h301, h303, h308, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h134, h135, h304, h308, hc24, hlam, hphi, u4elo4]
                        · linarith only [h134, h135, h236, h301, h303, h304, h307, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h134, h135, h236, h301, h303, h304, h306, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h236, h301, h303, h305, hlam]
                  · linarith only [h134, h135, h236, h301, h303, h304, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h134, h303, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h134, h135, h236, h301, h302, hc14, hlam, hphi, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h317 | h317
              · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
                · rcases m.htr 1 2 4 (by decide) (by decide) with h319 | h319
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h320 | h320
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h321 | h321
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h322 | h322
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
                          · linarith only [h134, h323, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h0, h134, h301, h320, h323, hc14, hlam, hphi, u4elo4]
                        · linarith only [h0, h134, h236, h318, h321, h322, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h0, h134, h236, h318, h319, h321, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h134, h236, h318, h319, h320, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h134, h236, h318, h319, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h134, h318, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h0, h134, h236, h317, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h134, h300, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h333 | h333
      · rcases m.htr 0 2 3 (by decide) (by decide) with h334 | h334
        · rcases m.htr 0 2 4 (by decide) (by decide) with h335 | h335
          · rcases m.htr 0 2 5 (by decide) (by decide) with h336 | h336
            · rcases m.htr 0 3 4 (by decide) (by decide) with h337 | h337
              · rcases m.htr 1 2 3 (by decide) (by decide) with h338 | h338
                · rcases m.htr 1 2 4 (by decide) (by decide) with h339 | h339
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h340 | h340
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h341 | h341
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h342 | h342
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h343 | h343
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h344 | h344
                            · linarith only [h334, h344, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h134, h333, h337, h340, h344, hc23, hc25, hlam, hphi, ht0b, ht34, ht5b, u0elo2, u4elo1]
                          · linarith only [h134, h333, h340, h343, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h134, h333, h340, h341, h342, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                      · linarith only [h334, h337, h341, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h336, h340, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h339, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h333, h334, h338, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h353 | h353
                · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h355 | h355
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h356 | h356
                      · linarith only [h334, h337, h356, hc23, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h358 | h358
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h359 | h359
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h360 | h360
                            · linarith only [h334, h356, h360, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h362 | h362
                              · linarith only [h335, h362, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h356, h359, h362, hc24, hlam, hphi, u4elo3]
                          · linarith only [h134, h333, h355, h359, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h134, h333, h353, h358, hc23, hlam, hphi, ht34, u4elo1]
                    · linarith only [h134, h336, h354, h355, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h333, h354, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                · linarith only [h0, h333, h334, h353, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
            · linarith only [h134, h333, h334, h336, hc23, hlam, hphi, ht34, u4elo1]
          · linarith only [h334, h335, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h372 | h372
          · rcases m.htr 0 2 5 (by decide) (by decide) with h373 | h373
            · rcases m.htr 0 3 4 (by decide) (by decide) with h374 | h374
              · rcases m.htr 1 2 3 (by decide) (by decide) with h375 | h375
                · rcases m.htr 1 2 4 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h378 | h378
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h379 | h379
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h380 | h380
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h381 | h381
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h382 | h382
                              · linarith only [h334, h372, h375, h382, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h380, h382, hc24, hlam, hphi, u4elo1]
                            · linarith only [h334, h372, h381, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h134, h333, h377, h380, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h334, h372, h375, h379, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h134, h333, h334, h372, h374, h375, h377, h378, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h134, h333, h334, h372, h375, h377, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h334, h372, h375, h376, hlam]
                · linarith only [h0, h333, h375, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h334, h372, h374, hc24, hlam, hphi, u4elo3]
            · linarith only [h134, h333, h372, h373, hlam]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h394 | h394
            · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
              · rcases m.htr 1 2 3 (by decide) (by decide) with h396 | h396
                · rcases m.htr 1 2 4 (by decide) (by decide) with h397 | h397
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h399 | h399
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h400 | h400
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h401 | h401
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h402 | h402
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h403 | h403
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h404 | h404
                                · linarith only [h395, h404, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h0, h333, h372, h397, h398, h403, h404, hc34, hlam, hphi, u4elo1]
                              · linarith only [h0, h333, h372, h398, h403, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h0, h333, h334, h398, h402, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h0, h333, h372, h397, h398, h401, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                        · linarith only [h0, h333, h334, h396, h398, h400, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                      · linarith only [h0, h333, h334, h395, h396, h398, h399, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h0, h333, h334, h396, h398, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h333, h334, h396, h397, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h333, h396, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h415 | h415
                · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h417 | h417
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h418 | h418
                      · linarith only [h0, h333, h334, h395, h417, h418, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h0, h333, h334, h415, h417, h418, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h0, h333, h334, h415, h417, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h333, h334, h415, h416, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h333, h415, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h0, h333, h394, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h425 | h425
        · rcases m.htr 0 2 4 (by decide) (by decide) with h426 | h426
          · rcases m.htr 0 2 5 (by decide) (by decide) with h427 | h427
            · rcases m.htr 0 3 4 (by decide) (by decide) with h428 | h428
              · rcases m.htr 1 2 3 (by decide) (by decide) with h429 | h429
                · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h431 | h431
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h432 | h432
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h433 | h433
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h434 | h434
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h435 | h435
                            · linarith only [h425, h435, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                            · linarith only [h428, h435, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h134, h434, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h134, h432, h433, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h425, h428, h432, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h427, h431, hlam]
                  · linarith only [h0, h426, h427, h430, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h0, h425, h429, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
                · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h446 | h446
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h447 | h447
                      · linarith only [h428, h447, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h449 | h449
                        · linarith only [h333, h447, h449, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h451 | h451
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h452 | h452
                            · linarith only [h425, h428, h452, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h454 | h454
                              · linarith only [h426, h454, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h451, h454, hc24, hlam, hphi, u4elo1]
                          · linarith only [h134, h451, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                    · linarith only [h0, h427, h446, hlam]
                  · linarith only [h0, h445, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h425, h444, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h461 | h461
              · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                · rcases m.htr 1 2 4 (by decide) (by decide) with h463 | h463
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h464 | h464
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h465 | h465
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h466 | h466
                        · linarith only [h425, h427, h464, h466, hc23, hlam, hphi, u3elo1]
                        · linarith only [h134, h465, h466, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h425, h461, h465, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h470 | h470
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h471 | h471
                        · linarith only [h462, h464, h471, hlam]
                        · linarith only [h134, h470, h471, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h425, h461, h470, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h426, h463, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h462, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
                · rcases m.htr 1 2 4 (by decide) (by decide) with h478 | h478
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h479 | h479
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h480 | h480
                      · linarith only [h461, h480, hc03, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h482 | h482
                        · linarith only [h427, h479, h480, h482, hc02, hlam, hphi, ht23, ht34, u4elo3]
                        · linarith only [h425, h427, h479, h482, hc23, hlam, hphi, u3elo4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h485 | h485
                      · linarith only [h425, h461, h485, hc23, hlam, hphi, u3elo1]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h487 | h487
                        · linarith only [h333, h485, h487, hc01, hlam, hphi, ht12, ht23, u3elo3]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h489 | h489
                          · linarith only [h478, h479, h489, hlam]
                          · linarith only [h134, h489, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                  · linarith only [h0, h478, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                · linarith only [h0, h425, h477, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · linarith only [h425, h426, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h495 | h495
          · rcases m.htr 0 2 5 (by decide) (by decide) with h496 | h496
            · rcases m.htr 0 3 4 (by decide) (by decide) with h497 | h497
              · rcases m.htr 1 2 3 (by decide) (by decide) with h498 | h498
                · rcases m.htr 1 2 4 (by decide) (by decide) with h499 | h499
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h502 | h502
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h503 | h503
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h504 | h504
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h505 | h505
                              · linarith only [h425, h495, h498, h505, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                              · linarith only [h503, h504, h505, hc34, hlam, hphi, u4elo1]
                            · linarith only [h425, h495, h504, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                          · linarith only [h134, h503, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h425, h495, h498, h502, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h425, h495, h497, h498, h501, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h425, h496, h498, h500, hlam]
                  · linarith only [h425, h495, h498, h499, hlam]
                · linarith only [h0, h498, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h425, h495, h497, hc24, hlam, hphi, u4elo3]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h516 | h516
              · rcases m.htr 1 2 3 (by decide) (by decide) with h517 | h517
                · rcases m.htr 1 2 4 (by decide) (by decide) with h518 | h518
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h519 | h519
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h520 | h520
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h521 | h521
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h522 | h522
                          · linarith only [h495, h496, h519, h522, hc24, hlam, hphi, u4elo1]
                          · linarith only [h134, h522, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h425, h495, h517, h521, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                      · linarith only [h425, h495, h516, h517, h520, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h425, h495, h517, h519, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h425, h495, h517, h518, hlam]
                · linarith only [h0, h517, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h425, h495, h516, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h531 | h531
            · rcases m.htr 0 3 4 (by decide) (by decide) with h532 | h532
              · rcases m.htr 1 2 3 (by decide) (by decide) with h533 | h533
                · rcases m.htr 1 2 4 (by decide) (by decide) with h534 | h534
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h535 | h535
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h536 | h536
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h537 | h537
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h538 | h538
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h539 | h539
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h540 | h540
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h541 | h541
                                · linarith only [h532, h541, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h495, h531, h534, h540, h541, hc34, hlam, hphi, u4elo1]
                              · linarith only [h495, h531, h540, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                            · linarith only [h425, h531, h539, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                          · linarith only [h134, h538, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h425, h531, h533, h537, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                      · linarith only [h425, h531, h532, h533, h536, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                    · linarith only [h425, h531, h533, h535, hlam]
                  · linarith only [h425, h531, h533, h534, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h533, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h552 | h552
                · rcases m.htr 1 2 4 (by decide) (by decide) with h553 | h553
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h554 | h554
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h555 | h555
                      · linarith only [h425, h531, h532, h555, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                      · linarith only [h425, h531, h552, h555, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                    · linarith only [h425, h531, h552, h554, hlam]
                  · linarith only [h425, h531, h552, h553, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h0, h552, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h561 | h561
              · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
                · rcases m.htr 1 2 4 (by decide) (by decide) with h563 | h563
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h564 | h564
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h565 | h565
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h566 | h566
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h567 | h567
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h569 | h569
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                                · linarith only [h561, h570, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h567, h570, hc34, hlam, hphi, u4elo1]
                              · linarith only [h567, h569, hc24, hlam, hphi, u4elo1]
                            · linarith only [h425, h568, hc02, hlam, hphi, ht23, ht34, u4elo3]
                          · linarith only [h134, h567, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                        · linarith only [h0, h425, h562, h566, hc01, hlam, hphi, ht12, ht23, u3elo4]
                      · linarith only [h0, h425, h561, h562, h565, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h425, h562, h564, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h425, h562, h563, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h562, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h581 | h581
                · rcases m.htr 1 2 4 (by decide) (by decide) with h582 | h582
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h583 | h583
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h584 | h584
                      · linarith only [h561, h584, hc03, hlam, hphi, u3elo1]
                      · linarith only [h0, h425, h581, h584, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h425, h581, h583, hc01, hc25, hlam, hphi, ht12]
                  · linarith only [h0, h425, h581, h582, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h581, hc01, hlam, hphi, ht12, ht23, u3elo2]

end R2N4
