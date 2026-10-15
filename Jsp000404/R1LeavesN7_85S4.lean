import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_L_L_I_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · linarith only [h1, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · linarith only [h0, h1, h3, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
          · linarith only [h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
            · linarith only [h6, h8, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
            · linarith only [h0, h1, h5, h8, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h11 | h11
          · linarith only [h11, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13 | h13
            · linarith only [h11, h13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
              · linarith only [h0, h1, h11, h15, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h17 | h17
                · linarith only [h0, h1, h11, h17, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h19 | h19
                  · linarith only [h0, h1, h13, h19, h5, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h21 | h21
                    · linarith only [h0, h1, h11, h15, h21, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h21, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h24 | h24
    · linarith only [h24, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h26 | h26
      · linarith only [h26, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h28 | h28
        · rcases m.htr 0 3 4 (by decide) (by decide) with h29 | h29
          · linarith only [h29, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h31 | h31
            · linarith only [h29, h31, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
            · linarith only [h26, h28, h31, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
          · linarith only [h34, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h36 | h36
            · linarith only [h34, h36, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
              · rcases m.htr 1 2 4 (by decide) (by decide) with h39 | h39
                · rcases m.htr 1 2 5 (by decide) (by decide) with h40 | h40
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h42 | h42
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h43 | h43
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h44 | h44
                          · linarith only [h0, h26, h34, h38, h44, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h26, h41, h44, hc01, hc13, hlam, hphi]
                        · linarith only [h34, h41, h43, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h34, h41, h42, hc35, hlam, hphi, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                      · linarith only [h41, h49, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h51 | h51
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h52 | h52
                          · linarith only [h24, h41, h52, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h54 | h54
                            · linarith only [h38, h49, h54, hlam]
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
                                    linarith only [h0, hlam, p58_1]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h26, hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [hc24, hlam, hphi, ht0b, ht45, ht5b, p58_1, u0elo1]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h28, hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    rcases p58_3 (m.d 0 2) (by simp) with h64 | h64
                                    · linarith only [h0, h64, hlam]
                                    · rcases p58_3 (m.d 1 2) (by simp) with h66 | h66
                                      · rcases p58_3 (m.d 2 3) (by simp) with h67 | h67
                                        · linarith only [h38, h67, hlam]
                                        · linarith only [h26, h67, hlam]
                                      · linarith only [h0, h66, hlam]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h0, h26, hc01, hc12, hlam, hphi, p58_1]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h0, h26, h54, h56, hc01, hc12, hlam, hphi, p58_1]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h0, h26, h54, hc01, hc12, hlam, hphi, p58_1]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h0, h38, hc01, hc12, hlam, hphi, p58_1]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h38, hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h52, hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h54, hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h0, h39, hc01, hc12, hlam, hphi, p58_1]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h39, hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h39, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p58_1, u3ehi2]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h0, h26, h39, h54, hc01, hc12, hlam, hphi, p58_1]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h0, h40, hc01, hc12, hlam, hphi, p58_1]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h40, hlam, p58_0]
                                  · have p58_0 := h58c.1
                                    have p58_1 := h58c.2.1
                                    have p58_2 := h58c.2.2.1
                                    have p58_3 := h58c.2.2.2
                                    linarith only [h0, h26, h40, hc01, hc12, hlam, hphi, p58_1]
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
                                · linarith only [h34, h57, hc45, hlam, hphi, ht34, u3ehi0]
                              · linarith only [h0, h26, h51, h52, h56, hc01, hc14, hlam, hphi]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                          · linarith only [h38, h41, h51, h92, hc45, hlam, hphi, ht34, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                            · linarith only [h38, h49, h94, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h96 | h96
                              · linarith only [h0, h26, h38, h41, h51, h96, hc01, hc24, hlam, hphi, ht12]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                                · linarith only [h0, h26, h38, h41, h51, h98, hc01, hc34, hlam, hphi, ht12, ht23]
                                · linarith only [h34, h98, hc45, hlam, hphi, ht34, u3ehi0]
                  · linarith only [h0, h26, h38, h40, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h26, h38, h39, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                  · linarith only [h0, h104, h28, h38, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h106 | h106
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h108 | h108
                        · linarith only [h103, h104, h108, hlam]
                        · linarith only [h106, h108, h34, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h106, h107, h34, hc35, hlam, hphi, u3ehi0]
                    · linarith only [h103, h106, h38, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h113 | h113
                  · linarith only [h0, h103, h113, h28, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h116 | h116
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h117 | h117
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
                                    linarith only [h0, hlam, p122_1]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h26, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h113, h120, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p122_1, u0elo1]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h28, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h113, h118, h120, hc02, hc23, hlam, hphi, p122_1]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h38, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h103, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h113, hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    rcases p122_3 (m.d 0 2) (by simp) with h133 | h133
                                    · linarith only [h133, hlam, p122_0]
                                    · rcases p122_3 (m.d 1 2) (by simp) with h135 | h135
                                      · linarith only [h135, h38, hlam]
                                      · linarith only [h0, h135, hlam]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h0, hc01, hc23, hlam, hphi, ht12, p122_1]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [hlam, p122_0]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h0, h120, h28, hc01, hc23, hlam, hphi, ht12, p122_1]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h0, h113, hc01, hc23, hlam, hphi, ht12, p122_1]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    rcases p122_3 (m.d 0 2) (by simp) with h142 | h142
                                    · linarith only [h142, hlam, p122_0]
                                    · rcases p122_3 (m.d 1 2) (by simp) with h144 | h144
                                      · linarith only [h103, h144, hlam]
                                      · linarith only [h0, h144, hlam]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h0, hc01, hc24, hlam, hphi, ht12, p122_1]
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
                                    linarith only [h0, h113, h118, hc01, hc23, hlam, hphi, ht12, p122_1]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    rcases p122_3 (m.d 0 2) (by simp) with h151 | h151
                                    · linarith only [h151, hlam, p122_0]
                                    · rcases p122_3 (m.d 1 2) (by simp) with h153 | h153
                                      · linarith only [h113, h153, hlam]
                                      · linarith only [h0, h153, hlam]
                                  · have p122_0 := h122c.1
                                    have p122_1 := h122c.2.1
                                    have p122_2 := h122c.2.2.1
                                    have p122_3 := h122c.2.2.2
                                    linarith only [h0, hc01, hc25, hlam, hphi, ht12, p122_1]
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
                                · linarith only [h121, h34, hc45, hlam, hphi, ht34, u3ehi0]
                              · linarith only [h103, h117, h120, hlam]
                            · linarith only [h115, h119, h38, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h115, h118, h38, hlam]
                        · linarith only [h115, h117, h34, hc45, hlam, hphi, ht34, u3ehi0]
                      · linarith only [h115, h116, h34, hc35, hlam, hphi, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h166 | h166
                      · linarith only [h115, h166, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h168 | h168
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h169 | h169
                          · linarith only [h115, h169, h24, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h169, h38, hc01, hc34, hlam, hphi, ht12, ht23]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                          · linarith only [h0, h115, h172, h38, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h172, h38, hc01, hc34, hlam, hphi, ht12, ht23]

theorem r1l7_20_12_13_15_H_R_L_I_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h11, h6, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h10, h9, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h1, h15, h4, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                        · linarith only [h17, h6, h9, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19 | h19
                          · linarith only [h0, h1, h15, h19, h4, h6, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                            · linarith only [h0, h21, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h23 | h23
                              · linarith only [h0, h1, h17, h21, h23, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                              · linarith only [h23, h9, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h0, h3, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h2, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                · rcases m.htr 1 2 5 (by decide) (by decide) with h29 | h29
                  · linarith only [h0, h1, h29, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h31 | h31
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h33 | h33
                        · linarith only [h0, h1, h28, h33, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h32, h33, h6, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h31, h32, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h28, h31, h6, hlam]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h38 | h38
                  · linarith only [h0, h1, h38, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h42 | h42
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h44 | h44
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                              · linarith only [h0, h1, h40, h45, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                              · linarith only [h0, h1, h42, h44, h45, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h48 | h48
                              · linarith only [h0, h1, h28, h4, h44, h48, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases h2bigk with h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c | h50c
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h1, h28, h4, h44, h5, hlam, p50_2]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h0, h41, h48, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1, u3ehi3]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  rcases p50_3 (m.d 0 2) (by simp) with h54 | h54
                                  · rcases p50_3 (m.d 1 2) (by simp) with h55 | h55
                                    · linarith only [h0, h55, hlam]
                                    · rcases p50_3 (m.d 2 3) (by simp) with h57 | h57
                                      · linarith only [h1, h57, hlam]
                                      · linarith only [h42, h57, hlam]
                                  · linarith only [h54, hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  rcases p50_3 (m.d 0 2) (by simp) with h61 | h61
                                  · rcases p50_3 (m.d 1 2) (by simp) with h62 | h62
                                    · linarith only [h0, h62, hlam]
                                    · rcases p50_3 (m.d 2 3) (by simp) with h64 | h64
                                      · linarith only [h1, h64, hlam]
                                      · linarith only [h43, h64, hlam]
                                  · linarith only [h61, hlam, p50_0]
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
                                  linarith only [h6, hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h28, hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h38, hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h1, hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  rcases p50_3 (m.d 0 2) (by simp) with h74 | h74
                                  · rcases p50_3 (m.d 1 2) (by simp) with h75 | h75
                                    · linarith only [h75, hlam, p50_0]
                                    · rcases p50_3 (m.d 2 3) (by simp) with h77 | h77
                                      · rcases p50_3 (m.d 2 4) (by simp) with h78 | h78
                                        · linarith only [h42, h78, hlam]
                                        · linarith only [h28, h78, hlam]
                                      · linarith only [h77, hlam, p50_0]
                                  · linarith only [h0, h74, hlam]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h0, h1, h28, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p50_1]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h0, h1, h38, h41, h48, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p50_1, u3ehi3]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h2, hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h0, h1, h4, h44, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p50_1]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h42, hlam, p50_1]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h44, hlam, p50_1]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h3, hlam, p50_0]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  rcases p50_3 (m.d 0 2) (by simp) with h92 | h92
                                  · rcases p50_3 (m.d 1 2) (by simp) with h93 | h93
                                    · linarith only [h93, hlam, p50_0]
                                    · rcases p50_3 (m.d 2 3) (by simp) with h95 | h95
                                      · rcases p50_3 (m.d 2 4) (by simp) with h96 | h96
                                        · linarith only [h44, h96, hlam]
                                        · linarith only [h28, h96, hlam]
                                      · linarith only [h6, h95, hlam]
                                  · linarith only [h0, h92, hlam]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h43, hlam, p50_1]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [h28, hc12, hc25, hlam, hphi, p50_1]
                                · have p50_0 := h50c.1
                                  have p50_1 := h50c.2.1
                                  have p50_2 := h50c.2.2.1
                                  have p50_3 := h50c.2.2.2
                                  linarith only [hlam, p50_0]
                          · linarith only [h41, h43, h6, hlam]
                        · linarith only [h41, h42, h6, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h40, h41, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                      · linarith only [h107, h40, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                        · linarith only [h0, h1, h109, h40, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                          · linarith only [h109, h111, hc34, hlam, hphi, u3ehi4]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h113 | h113
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h114 | h114
                              · rcases h2bigk with h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h1, h111, h114, h4, h6, hlam, p115_2]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  rcases p115_3 (m.d 0 2) (by simp) with h118 | h118
                                  · rcases p115_3 (m.d 1 2) (by simp) with h119 | h119
                                    · linarith only [h0, h119, hlam]
                                    · rcases p115_3 (m.d 2 3) (by simp) with h121 | h121
                                      · linarith only [h121, hlam, p115_0]
                                      · rcases p115_3 (m.d 2 4) (by simp) with h123 | h123
                                        · linarith only [h123, h2, hlam]
                                        · linarith only [h109, h123, hlam]
                                  · linarith only [h118, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h0, h113, hc01, hlam, hphi, ht0b, ht5b, p115_1, u5ehi4]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  rcases p115_3 (m.d 0 2) (by simp) with h128 | h128
                                  · rcases p115_3 (m.d 1 2) (by simp) with h129 | h129
                                    · linarith only [h0, h129, hlam]
                                    · rcases p115_3 (m.d 2 3) (by simp) with h131 | h131
                                      · linarith only [h1, h131, hlam]
                                      · rcases p115_3 (m.d 2 4) (by simp) with h133 | h133
                                        · linarith only [h133, h2, hlam]
                                        · linarith only [h113, h133, hlam]
                                  · linarith only [h128, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h0, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h6, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h28, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h38, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h1, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h0, h1, h111, h114, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p115_1]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h109, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h111, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h2, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  rcases p115_3 (m.d 0 2) (by simp) with h148 | h148
                                  · rcases p115_3 (m.d 1 2) (by simp) with h149 | h149
                                    · linarith only [h149, hlam, p115_0]
                                    · rcases p115_3 (m.d 2 3) (by simp) with h151 | h151
                                      · linarith only [h109, h151, hlam]
                                      · linarith only [h151, h6, hlam]
                                  · linarith only [h0, h148, hlam]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p115_1, u3ehi2]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h0, h1, h109, h4, hc01, hlam, hphi, ht0b, ht5b, p115_1, u5ehi2]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h3, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  rcases p115_3 (m.d 0 2) (by simp) with h159 | h159
                                  · rcases p115_3 (m.d 1 2) (by simp) with h160 | h160
                                    · linarith only [h160, hlam, p115_0]
                                    · rcases p115_3 (m.d 2 3) (by simp) with h162 | h162
                                      · linarith only [h111, h162, hlam]
                                      · linarith only [h162, h6, hlam]
                                  · linarith only [h0, h159, hlam]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h6, hc12, hc25, hlam, hphi, p115_1]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [h113, hlam, p115_0]
                                · have p115_0 := h115c.1
                                  have p115_1 := h115c.2.1
                                  have p115_2 := h115c.2.2.1
                                  have p115_3 := h115c.2.2.2
                                  linarith only [hlam, p115_0]
                              · linarith only [h0, h1, h114, h4, h40, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h170 | h170
                              · linarith only [h0, h1, h113, h170, h28, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                              · linarith only [h0, h1, h170, h4, h40, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h1, h3, hc25, hlam, hphi, ht01, ht12, u0ehi2]
      · linarith only [h1, h2, hc24, hlam, hphi, ht01, ht12, u0ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht01, ht12, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_12_13_15_H_R_L_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h0, h10, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h2, h3, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                      · linarith only [h0, h13, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h0, h17, h6, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                        · linarith only [h16, h19, h6, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
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
                                  · linarith only [h28, h3, hlam]
                                  · rcases p21_3 (m.d 3 5) (by simp) with h30 | h30
                                    · linarith only [h30, h4, hlam]
                                    · linarith only [h30, h8, hlam]
                            · linarith only [h1, h23, hlam]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            rcases p21_3 (m.d 0 3) (by simp) with h34 | h34
                            · rcases p21_3 (m.d 1 3) (by simp) with h35 | h35
                              · linarith only [h1, h35, hlam]
                              · linarith only [h35, h6, hlam]
                            · linarith only [h2, h34, hlam]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h16, h19, h3, h5, h6, h8, hlam, p21_2]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h0, h16, h2, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p21_1, u2ehi3]
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
                            linarith only [h16, h8, hc35, hlam, hphi, ht23, p21_1, u2ehi3]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h0, h19, h2, h3, h5, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h8, hlam, p21_0]
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
                            linarith only [h0, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h17, hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h3, hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h6, hc34, hlam, hphi, ht23, p21_1, u2ehi2]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h16, hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h19, hlam, p21_1]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h4, hlam, p21_0]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h0, h19, h2, h3, h5, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p21_1, u2ehi2]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [h0, h16, h19, h2, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p21_1, u2ehi3]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            rcases p21_3 (m.d 0 3) (by simp) with h59 | h59
                            · rcases p21_3 (m.d 1 3) (by simp) with h60 | h60
                              · linarith only [h60, h8, hlam]
                              · linarith only [h16, h6, h60, hlam]
                            · linarith only [h3, h59, hlam]
                          · have p21_0 := h21c.1
                            have p21_1 := h21c.2.1
                            have p21_2 := h21c.2.2.1
                            have p21_3 := h21c.2.2.2
                            linarith only [hlam, p21_0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h0, h16, h2, h3, h65, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi1]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                        · rcases h3bigk with h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c | h68c
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 3) (by simp) with h70 | h70
                            · rcases p68_3 (m.d 1 3) (by simp) with h71 | h71
                              · linarith only [h1, h71, hlam]
                              · rcases p68_3 (m.d 2 3) (by simp) with h73 | h73
                                · linarith only [h2, h73, hlam]
                                · rcases p68_3 (m.d 3 4) (by simp) with h75 | h75
                                  · linarith only [h3, h75, hlam]
                                  · linarith only [h67, h75, h8, hlam]
                            · linarith only [h1, h70, hlam]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            rcases p68_3 (m.d 0 3) (by simp) with h79 | h79
                            · rcases p68_3 (m.d 1 3) (by simp) with h80 | h80
                              · linarith only [h1, h80, hlam]
                              · linarith only [h6, h80, hlam]
                            · linarith only [h2, h79, hlam]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h67, hc01, hlam, hphi, ht0b, ht5b, p68_1, u5ehi4]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u2ehi2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h1, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h67, h8, hc34, hlam, hphi, ht23, p68_1, u2ehi2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h67, h8, hlam, p68_1]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h8, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h2, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h6, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h16, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h65, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h3, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h3, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u2ehi2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u2ehi2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht5b, p68_1, u5ehi3]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h4, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h6, hc35, hlam, hphi, ht23, p68_1, u2ehi2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p68_1, u2ehi2]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [h67, hlam, p68_0]
                          · have p68_0 := h68c.1
                            have p68_1 := h68c.2.1
                            have p68_2 := h68c.2.2.1
                            have p68_3 := h68c.2.2.2
                            linarith only [hlam, p68_0]
                        · linarith only [h0, h16, h2, h3, h5, h67, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h6, h7, hc25, hlam, hphi, u2ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                · linarith only [h108, h6, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h112 | h112
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h113 | h113
                        · linarith only [h0, h111, h113, h2, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                        · rcases h3bigk with h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h0, h110, h2, hc01, hlam, hphi, ht0b, ht5b, p115_1, u5ehi3]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h0, h108, h112, h2, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p115_1, u2ehi1]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            rcases p115_3 (m.d 0 3) (by simp) with h119 | h119
                            · rcases p115_3 (m.d 1 3) (by simp) with h120 | h120
                              · linarith only [h1, h120, hlam]
                              · linarith only [h110, h113, h120, hlam]
                            · linarith only [h119, hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            rcases p115_3 (m.d 0 3) (by simp) with h124 | h124
                            · rcases p115_3 (m.d 1 3) (by simp) with h125 | h125
                              · linarith only [h1, h125, hlam]
                              · linarith only [h110, h125, hlam]
                            · linarith only [h124, hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h1, hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h6, hlam, p115_1]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            rcases p115_3 (m.d 0 3) (by simp) with h132 | h132
                            · rcases p115_3 (m.d 1 3) (by simp) with h133 | h133
                              · rcases p115_3 (m.d 2 3) (by simp) with h134 | h134
                                · rcases p115_3 (m.d 3 4) (by simp) with h135 | h135
                                  · linarith only [h135, hlam, p115_0]
                                  · rcases p115_3 (m.d 3 5) (by simp) with h137 | h137
                                    · linarith only [h110, h137, hlam]
                                    · linarith only [h113, h137, hlam]
                                · linarith only [h111, h134, hlam]
                              · linarith only [h133, hlam, p115_0]
                            · linarith only [h132, h3, hlam]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h0, h2, h6, hc01, hlam, hphi, ht0b, ht5b, p115_1, u5ehi3]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h2, hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h0, h2, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p115_1, u2ehi1]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            rcases p115_3 (m.d 0 3) (by simp) with h147 | h147
                            · rcases p115_3 (m.d 1 3) (by simp) with h148 | h148
                              · linarith only [h148, h6, hlam]
                              · linarith only [h0, h110, h148, h2, hc01, hlam, hphi, ht0b, ht5b, p115_1, u5ehi3]
                            · linarith only [h147, h3, hlam]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p115_1, u5ehi3]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h3, hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h110, h113, hlam, p115_1]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h111, hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h113, hlam, p115_1]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h4, hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h110, hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h112, hlam, p115_0]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [h1, h110, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p115_1]
                          · have p115_0 := h115c.1
                            have p115_1 := h115c.2.1
                            have p115_2 := h115c.2.2.1
                            have p115_3 := h115c.2.2.2
                            linarith only [hlam, p115_0]
                      · linarith only [h110, h112, h6, hlam]
                    · linarith only [h0, h110, h111, h2, h3, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                      · linarith only [h110, h166, h6, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h0, h166, h2, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                    · linarith only [h165, h6, hc34, hlam, hphi, ht23, u2ehi1]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_12_13_15_H_R_L_R_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h10, h13, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16 | h16
                            · linarith only [h0, h16, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h10, h16, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h10, h11, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h20 | h20
                        · linarith only [h0, h10, h2, h20, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h22 | h22
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h23 | h23
                            · linarith only [h10, h23, h7, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                              · linarith only [h20, h25, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h27 | h27
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                                  · rcases h5bigk with h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c | h29c
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      rcases p29_3 (m.d 0 5) (by simp) with h31 | h31
                                      · rcases p29_3 (m.d 1 5) (by simp) with h32 | h32
                                        · linarith only [h32, hlam, p29_0]
                                        · rcases p29_3 (m.d 2 5) (by simp) with h34 | h34
                                          · linarith only [h34, h4, hlam]
                                          · rcases p29_3 (m.d 3 5) (by simp) with h36 | h36
                                            · linarith only [h36, h6, hlam]
                                            · linarith only [h20, h36, hlam]
                                      · linarith only [h31, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      rcases p29_3 (m.d 0 5) (by simp) with h40 | h40
                                      · rcases p29_3 (m.d 1 5) (by simp) with h41 | h41
                                        · linarith only [h0, h25, h41, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi2]
                                        · linarith only [h41, h9, hlam]
                                      · linarith only [h4, h40, hlam]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h2, h20, h6, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p29_1, u3ehi1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      rcases p29_3 (m.d 0 5) (by simp) with h46 | h46
                                      · rcases p29_3 (m.d 1 5) (by simp) with h47 | h47
                                        · linarith only [h0, h2, h20, h47, h6, hc01, hlam, hphi, u0ehi4]
                                        · linarith only [h22, h47, hlam]
                                      · linarith only [h46, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h10, h2, h22, h5, hc01, hlam, hphi, p29_1, u0ehi4]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h10, h2, h22, h25, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi2]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h20, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      rcases p29_3 (m.d 0 5) (by simp) with h55 | h55
                                      · rcases p29_3 (m.d 1 5) (by simp) with h56 | h56
                                        · rcases p29_3 (m.d 2 5) (by simp) with h57 | h57
                                          · linarith only [h57, h9, hlam]
                                          · linarith only [h27, h57, hlam]
                                        · linarith only [h22, h56, hlam]
                                      · linarith only [h27, h55, hc24, hlam, hphi, ht01, ht12, u0ehi4]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h4, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h9, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h25, hlam, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h27, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p29_1]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h6, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h2, h28, h5, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi4]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h2, h28, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p29_1, u2ehi4]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      rcases p29_3 (m.d 0 5) (by simp) with h71 | h71
                                      · rcases p29_3 (m.d 1 5) (by simp) with h72 | h72
                                        · linarith only [h20, h72, hlam]
                                        · linarith only [h22, h72, hlam]
                                      · linarith only [h0, h10, h2, h22, h5, h71, hc01, hlam, hphi, u0ehi4]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h0, h27, h8, hc01, hlam, hphi, p29_1, u0ehi4]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h22, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h27, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [h28, hlam, p29_0]
                                    · have p29_0 := h29c.1
                                      have p29_1 := h29c.2.1
                                      have p29_2 := h29c.2.2.1
                                      have p29_3 := h29c.2.2.2
                                      linarith only [hlam, p29_0]
                                  · linarith only [h0, h10, h27, h28, h8, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · linarith only [h0, h22, h27, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                            · linarith only [h20, h7, h83, hc35, hlam, hphi, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                              · linarith only [h20, h7, h85, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                                · linarith only [h0, h22, h8, h87, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h89 | h89
                                  · linarith only [h10, h22, h89, hc34, hlam, hphi, u3ehi1]
                                  · linarith only [h10, h7, h89, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h7, h8, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                  · linarith only [h7, h94, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                    · linarith only [h0, h2, h7, h96, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h103 | h103
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h104 | h104
                                  · rcases h5bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      rcases p105_3 (m.d 0 5) (by simp) with h107 | h107
                                      · rcases p105_3 (m.d 1 5) (by simp) with h108 | h108
                                        · linarith only [h108, hlam, p105_0]
                                        · rcases p105_3 (m.d 2 5) (by simp) with h110 | h110
                                          · linarith only [h110, h4, hlam]
                                          · linarith only [h110, h96, hlam]
                                      · linarith only [h107, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h2, h6, h96, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      rcases p105_3 (m.d 0 5) (by simp) with h115 | h115
                                      · rcases p105_3 (m.d 1 5) (by simp) with h116 | h116
                                        · linarith only [h0, h100, h101, h116, h2, h94, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p105_1, u3ehi4]
                                        · linarith only [h116, h99, hlam]
                                      · linarith only [h115, h6, hlam]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      rcases p105_3 (m.d 0 5) (by simp) with h120 | h120
                                      · rcases p105_3 (m.d 1 5) (by simp) with h121 | h121
                                        · linarith only [h1, h100, h121, h98, hc01, hlam, hphi, u0ehi4]
                                        · linarith only [h100, h121, hlam]
                                      · linarith only [h120, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, p105_1, u0ehi4]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h96, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h1, h99, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p105_1, u3ehi4]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      rcases p105_3 (m.d 0 5) (by simp) with h129 | h129
                                      · rcases p105_3 (m.d 1 5) (by simp) with h130 | h130
                                        · rcases p105_3 (m.d 2 5) (by simp) with h131 | h131
                                          · rcases p105_3 (m.d 3 5) (by simp) with h132 | h132
                                            · linarith only [h132, h99, hlam]
                                            · linarith only [h104, h132, hlam]
                                          · linarith only [h103, h131, hlam]
                                        · linarith only [h100, h130, hlam]
                                      · linarith only [h104, h129, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h4, hlam, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h103, h3, h96, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h101, h103, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p105_1, u3ehi4]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      rcases p105_3 (m.d 0 5) (by simp) with h142 | h142
                                      · rcases p105_3 (m.d 1 5) (by simp) with h143 | h143
                                        · linarith only [h143, h96, hlam]
                                        · linarith only [h100, h143, hlam]
                                      · linarith only [h0, h101, h103, h142, h2, hc01, hlam, hphi, p105_1, u0ehi4]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h6, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h99, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h102, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h2, h7, h99, hc01, hc45, hlam, hphi, ht0b, ht5b, p105_1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h0, h101, h103, h2, h96, hc01, hc45, hlam, hphi, ht23, ht34, p105_1, u0ehi4, u2ehi1]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h100, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h103, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [h104, hlam, p105_0]
                                    · have p105_0 := h105c.1
                                      have p105_1 := h105c.2.1
                                      have p105_2 := h105c.2.2.1
                                      have p105_3 := h105c.2.2.2
                                      linarith only [hlam, p105_0]
                                  · linarith only [h0, h100, h101, h104, h2, h94, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h100, h103, h94, hlam]
                              · linarith only [h0, h102, h2, h6, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h101, h7, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h162 | h162
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h163 | h163
                                · linarith only [h100, h161, h163, h94, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h163, h94, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h162, h7, h99, hlam]
                            · linarith only [h161, h7, h99, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h98, h99, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h169 | h169
                        · linarith only [h0, h169, h2, h5, h98, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h171 | h171
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h172 | h172
                            · linarith only [h0, h172, h2, h7, h98, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h172, h7, hc34, hlam, hphi, ht23, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                            · linarith only [h175, h7, h98, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h0, h175, h2, h5, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · linarith only [h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc25, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h2, h3, hc24, hlam, hphi, ht01, ht12, u0ehi2]
      · linarith only [h2, hc23, hlam, hphi, ht01, ht12, u0ehi1]
    · linarith only [h1, hc13, hlam, hphi, ht01, u0ehi0]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_12_13_15_M_LI_L_0_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
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
  have h3ehi := hb3.1
  have h5ehi := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · linarith only [h3, h6, hc12, hlam, hphi, u2elo0]
            · linarith only [h4, h5, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h10 | h10
            · linarith only [h10, h4, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
              · linarith only [h0, h12, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · linarith only [h12, h3, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h15 | h15
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16 | h16
            · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
              · linarith only [h15, h17, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h19 | h19
                · rcases m.htr 1 3 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h1, h20, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                  · linarith only [h15, h20, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                  · linarith only [h1, h23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                  · linarith only [h15, h23, h3, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
            · linarith only [h15, h16, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h27 | h27
            · linarith only [h15, h27, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
              · linarith only [h0, h29, h3, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h31 | h31
                · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                  · linarith only [h1, h15, h32, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                  · linarith only [h29, h31, h32, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h35 | h35
                  · linarith only [h1, h15, h3, h35, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h1, h27, h37, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h2, h39, hlam, hphi, ht0b, ht5b, u0elo0, u5ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                        · linarith only [h1, h15, h41, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                          · linarith only [h1, h27, h43, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                            · linarith only [h31, h39, h45, hc12, hlam, hphi, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                              · linarith only [h0, h3, h41, h45, h47, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h1, h15, h47, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h50 | h50
        · rcases m.htr 0 3 4 (by decide) (by decide) with h51 | h51
          · linarith only [h0, h2, h50, h51, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h53 | h53
            · linarith only [h51, h53, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
              · linarith only [h0, h55, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
              · linarith only [h50, h55, hc12, hlam, hphi, u2elo0]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h58 | h58
          · linarith only [h1, h2, h58, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h60 | h60
            · linarith only [h58, h60, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
              · linarith only [h50, h62, hc02, hlam, hphi, u2elo1]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                · linarith only [h0, h2, h50, h64, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1, h2, h64, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h67 | h67
      · rcases m.htr 0 2 3 (by decide) (by decide) with h68 | h68
        · linarith only [h0, h1, h68, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h70 | h70
          · rcases m.htr 0 3 5 (by decide) (by decide) with h71 | h71
            · rcases m.htr 1 2 3 (by decide) (by decide) with h72 | h72
              · linarith only [h68, h72, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1, h72, hc12, hlam, hphi, u2elo2]
            · linarith only [h70, h71, hc35, hlam, hphi, u3ehi3]
          · linarith only [h1, h67, h70, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h77 | h77
        · linarith only [h0, h1, h77, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h79 | h79
          · rcases m.htr 0 3 5 (by decide) (by decide) with h80 | h80
            · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
              · linarith only [h77, h81, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h1, h81, hc12, hlam, hphi, u2elo2]
            · linarith only [h79, h80, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h85 | h85
            · linarith only [h79, h85, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
              · linarith only [h0, h77, h87, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
              · linarith only [h0, h1, h87, hc12, hlam, hphi, u2elo2]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h90 | h90
    · linarith only [h0, h90, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h92 | h92
      · rcases m.htr 0 2 3 (by decide) (by decide) with h93 | h93
        · rcases m.htr 0 3 4 (by decide) (by decide) with h94 | h94
          · rcases m.htr 0 3 5 (by decide) (by decide) with h95 | h95
            · rcases m.htr 1 2 3 (by decide) (by decide) with h96 | h96
              · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                · rcases m.htr 1 3 4 (by decide) (by decide) with h98 | h98
                  · linarith only [h90, h92, h96, h98, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi3]
                  · linarith only [h90, h93, h94, h98, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h0, h93, h95, h97, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
              · linarith only [h0, h93, h95, h96, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi4]
            · linarith only [h94, h95, hc35, hlam, hphi, u3ehi3]
          · linarith only [h90, h92, h94, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h105 | h105
          · rcases m.htr 0 3 5 (by decide) (by decide) with h106 | h106
            · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
              · linarith only [h107, h93, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h107, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h105, h106, hc35, hlam, hphi, u3ehi3]
          · linarith only [h105, h90, h92, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h112 | h112
        · rcases m.htr 0 3 4 (by decide) (by decide) with h113 | h113
          · rcases m.htr 0 3 5 (by decide) (by decide) with h114 | h114
            · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
              · rcases m.htr 1 2 4 (by decide) (by decide) with h116 | h116
                · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h118 | h118
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h119 | h119
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h120 | h120
                        · linarith only [h112, h120, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h113, h120, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
                        · linarith only [h112, h123, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                        · linarith only [h113, h123, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                    · linarith only [h114, h118, h90, hlam]
                  · linarith only [h113, h117, h90, hlam]
                · linarith only [h0, h112, h114, h116, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi3]
              · linarith only [h0, h112, h113, h115, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2, u3ehi3]
            · linarith only [h113, h114, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h131 | h131
            · linarith only [h113, h131, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h133 | h133
              · rcases m.htr 1 2 4 (by decide) (by decide) with h134 | h134
                · rcases m.htr 1 3 4 (by decide) (by decide) with h135 | h135
                  · linarith only [h113, h133, h135, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h137 | h137
                    · linarith only [h112, h131, h133, h137, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h139 | h139
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                        · linarith only [h112, h135, h140, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                          · linarith only [h0, h112, h137, h142, h90, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                            · linarith only [h134, h144, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                            · linarith only [h134, h139, h140, h144, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                        · linarith only [h0, h112, h135, h147, h90, hc01, hlam, hphi, ht12, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                          · linarith only [h0, h112, h137, h149, h90, hc01, hlam, hphi, ht12, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h151 | h151
                            · linarith only [h139, h151, h92, hc01, hlam, hphi, ht12, u2elo3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h153 | h153
                              · linarith only [h0, h112, h135, h139, h153, h90, hc01, hc34, hlam, hphi, ht12, u2elo1, u3ehi2]
                              · linarith only [h113, h153, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h0, h112, h134, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3, u3ehi2]
              · linarith only [h0, h112, h133, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
          · rcases m.htr 0 3 5 (by decide) (by decide) with h159 | h159
            · rcases m.htr 1 2 3 (by decide) (by decide) with h160 | h160
              · linarith only [h112, h160, hc02, hlam, hphi, u2elo1]
              · linarith only [h0, h160, hc01, hlam, hphi, ht12, u2elo2]
            · linarith only [h158, h159, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
            · linarith only [h158, h164, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
              · linarith only [h0, h112, h166, hc01, hlam, hphi, ht12, u2elo1]
              · linarith only [h0, h166, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
