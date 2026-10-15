import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_R_L_R_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 4 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h5, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h5, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                  · linarith only [h0, h13, h2, h3, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                    · linarith only [h15, h5, h7, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17 | h17
                      · linarith only [h13, h17, h5, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                        · rcases h3bigk with h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c | h20c
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            rcases p20_3 (m.d 0 3) (by simp) with h22 | h22
                            · rcases p20_3 (m.d 1 3) (by simp) with h23 | h23
                              · linarith only [h1, h23, hlam]
                              · rcases p20_3 (m.d 2 3) (by simp) with h25 | h25
                                · linarith only [h2, h25, hlam]
                                · rcases p20_3 (m.d 3 4) (by simp) with h27 | h27
                                  · linarith only [h27, h3, hlam]
                                  · linarith only [h27, h7, hlam]
                            · linarith only [h1, h22, hlam]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            rcases p20_3 (m.d 0 3) (by simp) with h31 | h31
                            · rcases p20_3 (m.d 1 3) (by simp) with h32 | h32
                              · linarith only [h1, h32, hlam]
                              · linarith only [h32, h5, hlam]
                            · linarith only [h2, h31, hlam]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h0, h13, h19, h2, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p20_1, u2ehi2]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h0, h13, h2, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p20_1, u2ehi2]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h1, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h13, h19, hc34, hlam, hphi, ht23, p20_1, u2ehi2]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h7, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h13, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h2, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h5, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h15, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h17, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h3, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p20_1, u3ehi1]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p20_1, u2ehi2]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p20_1, u3ehi4]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h4, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h5, hc35, hlam, hphi, ht23, p20_1, u2ehi2]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p20_1, u2ehi2]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [h19, hlam, p20_0]
                          · have p20_0 := h20c.1
                            have p20_1 := h20c.2.1
                            have p20_2 := h20c.2.2.1
                            have p20_3 := h20c.2.2.2
                            linarith only [hlam, p20_0]
                        · linarith only [h19, h5, h7, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h5, h6, hc24, hlam, hphi, u2ehi2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
              · linarith only [h5, h60, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h62 | h62
                · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h64 | h64
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h66 | h66
                        · rcases h3bigk with h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c | h67c
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h0, h2, h62, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1, u3ehi4]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h0, h2, h60, h64, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p67_1, u2ehi1]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            rcases p67_3 (m.d 0 3) (by simp) with h71 | h71
                            · rcases p67_3 (m.d 1 3) (by simp) with h72 | h72
                              · linarith only [h1, h72, hlam]
                              · linarith only [h62, h72, hlam]
                            · linarith only [h71, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            rcases p67_3 (m.d 0 3) (by simp) with h76 | h76
                            · rcases p67_3 (m.d 1 3) (by simp) with h77 | h77
                              · linarith only [h1, h77, hlam]
                              · linarith only [h63, h77, hlam]
                            · linarith only [h76, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h1, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h5, hlam, p67_1]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h1, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1, u3ehi4]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1, u3ehi4]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h2, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1, u3ehi1]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h0, h2, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1, u3ehi4]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p67_1, u3ehi4]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h3, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h62, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h64, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h62, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p67_1, u3ehi4]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h4, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h63, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h65, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [h66, hlam, p67_0]
                          · have p67_0 := h67c.1
                            have p67_1 := h67c.2.1
                            have p67_2 := h67c.2.2.1
                            have p67_3 := h67c.2.2.2
                            linarith only [hlam, p67_0]
                        · rcases h3bigk with h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c | h101c
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h0, h2, h63, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi3]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h0, h2, h60, h64, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p101_1, u2ehi1]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            rcases p101_3 (m.d 0 3) (by simp) with h105 | h105
                            · rcases p101_3 (m.d 1 3) (by simp) with h106 | h106
                              · linarith only [h1, h106, hlam]
                              · linarith only [h106, h62, hlam]
                            · linarith only [h105, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            rcases p101_3 (m.d 0 3) (by simp) with h110 | h110
                            · rcases p101_3 (m.d 1 3) (by simp) with h111 | h111
                              · linarith only [h1, h111, hlam]
                              · linarith only [h111, h63, hlam]
                            · linarith only [h110, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h1, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h5, hlam, p101_1]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi3]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h1, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi3]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h2, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi1]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi3]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h0, h2, h66, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p101_1, u3ehi3]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h3, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h62, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h64, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h66, hlam, p101_1]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h4, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h63, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h65, hlam, p101_0]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [h63, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p101_1, u3ehi3]
                          · have p101_0 := h101c.1
                            have p101_1 := h101c.2.1
                            have p101_2 := h101c.2.2.1
                            have p101_3 := h101c.2.2.2
                            linarith only [hlam, p101_0]
                      · linarith only [h5, h63, h65, hlam]
                    · linarith only [h5, h63, h64, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h62, h63, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h138 | h138
                  · linarith only [h0, h138, h2, h3, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h140 | h140
                    · linarith only [h140, h5, h62, hc23, hlam, hphi, u2ehi1]
                    · linarith only [h0, h140, h2, h3, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
          · linarith only [h3, h4, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h144 | h144
          · linarith only [h144, h3, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
            · rcases m.htr 1 2 4 (by decide) (by decide) with h147 | h147
              · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                · linarith only [h148, h3, hc13, hlam, hphi, ht01, u0ehi2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h150 | h150
                  · linarith only [h1, h144, h150, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi4]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                    · linarith only [h0, h146, h152, h3, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h154 | h154
                      · linarith only [h144, h146, h154, hc13, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h156 | h156
                        · rcases h3bigk with h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c | h157c
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h144, h146, h156, hc34, hlam, hphi, p157_1, u3ehi2]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h144, h156, hc34, hlam, hphi, ht23, p157_1, u2ehi2]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h3, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h144, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h1, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p157_1, u2ehi2]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h148, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h150, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h2, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h146, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h152, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h154, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hc34, hlam, hphi, p157_1, u3ehi0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h146, hc34, hlam, hphi, ht23, p157_1, u2ehi2]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hc34, hlam, hphi, ht23, p157_1, u2ehi2]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hc34, hlam, hphi, p157_1, u3ehi4]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p157_1, u0ehi2]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h146, hc35, hlam, hphi, ht23, p157_1, u2ehi2]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hc35, hlam, hphi, ht23, p157_1, u2ehi2]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [h156, hlam, p157_0]
                          · have p157_0 := h157c.1
                            have p157_1 := h157c.2.1
                            have p157_2 := h157c.2.2.1
                            have p157_3 := h157c.2.2.2
                            linarith only [hlam, p157_0]
                        · linarith only [h156, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
              · linarith only [h146, h147, hc24, hlam, hphi, u2ehi2]
            · linarith only [h146, h2, h3, hc34, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h186 | h186
        · rcases m.htr 0 3 5 (by decide) (by decide) with h187 | h187
          · rcases m.htr 1 2 3 (by decide) (by decide) with h188 | h188
            · linarith only [h188, h2, hc12, hlam, hphi, ht01, u0ehi1]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h190 | h190
              · linarith only [h0, h190, h2, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h192 | h192
                · rcases m.htr 1 3 5 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h195 | h195
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h196 | h196
                        · rcases h3bigk with h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c | h197c
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h192, h196, hc03, hc45, hlam, hphi, ht0b, ht5b, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h2, hlam, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            rcases p197_3 (m.d 0 3) (by simp) with h201 | h201
                            · rcases p197_3 (m.d 1 3) (by simp) with h202 | h202
                              · linarith only [h1, h202, hlam]
                              · linarith only [h192, h202, hlam]
                            · linarith only [h201, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            rcases p197_3 (m.d 0 3) (by simp) with h206 | h206
                            · rcases p197_3 (m.d 1 3) (by simp) with h207 | h207
                              · linarith only [h1, h207, hlam]
                              · linarith only [h193, h207, hlam]
                            · linarith only [h206, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h1, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h188, hlam, p197_1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h1, h196, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1, u3ehi4]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p197_1, u3ehi4]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p197_1, u0ehi2]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h188, hc23, hlam, hphi, p197_1, u2ehi1]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            rcases p197_3 (m.d 0 3) (by simp) with h219 | h219
                            · linarith only [h2, h219, hlam]
                            · linarith only [h186, h219, hlam]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            rcases p197_3 (m.d 0 3) (by simp) with h222 | h222
                            · linarith only [h2, h222, hlam]
                            · linarith only [h187, h222, hlam]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h186, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h192, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h194, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h192, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p197_1, u3ehi4]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h187, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h193, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h195, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [h196, hlam, p197_0]
                          · have p197_0 := h197c.1
                            have p197_1 := h197c.2.1
                            have p197_2 := h197c.2.2.1
                            have p197_3 := h197c.2.2.2
                            linarith only [hlam, p197_0]
                        · rcases h3bigk with h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c | h235c
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h193, h196, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p235_1, u3ehi3]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h2, hlam, p235_1]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            rcases p235_3 (m.d 0 3) (by simp) with h239 | h239
                            · rcases p235_3 (m.d 1 3) (by simp) with h240 | h240
                              · linarith only [h1, h240, hlam]
                              · linarith only [h192, h240, hlam]
                            · linarith only [h239, hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            rcases p235_3 (m.d 0 3) (by simp) with h244 | h244
                            · rcases p235_3 (m.d 1 3) (by simp) with h245 | h245
                              · linarith only [h1, h245, hlam]
                              · linarith only [h193, h245, hlam]
                            · linarith only [h244, hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h1, hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h188, hlam, p235_1]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p235_1, u3ehi3]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h1, h196, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p235_1, u3ehi3]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [hc23, hlam, hphi, ht01, ht12, p235_1, u0ehi2]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h188, hc23, hlam, hphi, p235_1, u2ehi1]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            rcases p235_3 (m.d 0 3) (by simp) with h257 | h257
                            · linarith only [h2, h257, hlam]
                            · linarith only [h186, h257, hlam]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            rcases p235_3 (m.d 0 3) (by simp) with h260 | h260
                            · linarith only [h2, h260, hlam]
                            · linarith only [h187, h260, hlam]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h186, hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h192, hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h194, hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h196, hlam, p235_1]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h187, hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h193, hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h195, hlam, p235_0]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [h1, h193, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p235_1, u3ehi3]
                          · have p235_0 := h235c.1
                            have p235_1 := h235c.2.1
                            have p235_2 := h235c.2.2.1
                            have p235_3 := h235c.2.2.2
                            linarith only [hlam, p235_0]
                      · linarith only [h1, h193, h195, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h194, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h192, h193, hc35, hlam, hphi, u3ehi3]
                · linarith only [h186, h188, h192, h2, hc23, hlam, hphi, u2ehi1]
          · linarith only [h186, h187, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h278 | h278
          · linarith only [h186, h278, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h280 | h280
            · linarith only [h0, h2, h280, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h282 | h282
              · linarith only [h0, h186, h2, h282, hc34, hlam, hphi, ht23, u2ehi3]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h284 | h284
                · linarith only [h186, h2, h284, hc13, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h286 | h286
                  · linarith only [h1, h278, h286, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h288 | h288
                    · linarith only [h186, h2, h288, hc23, hlam, hphi, ht01, ht12, u0ehi1]
                    · linarith only [h2, h288, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h291 | h291
      · linarith only [h0, h1, h291, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h293 | h293
        · rcases m.htr 0 3 5 (by decide) (by decide) with h294 | h294
          · rcases m.htr 1 2 3 (by decide) (by decide) with h295 | h295
            · linarith only [h291, h295, hc12, hlam, hphi, ht01, u0ehi1]
            · linarith only [h0, h1, h295, hc23, hlam, hphi, u2ehi1]
          · linarith only [h0, h1, h294, hc35, hlam, hphi, ht23, u2ehi1]
        · linarith only [h0, h1, h293, hc34, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h300 | h300
    · rcases m.htr 0 2 3 (by decide) (by decide) with h301 | h301
      · rcases m.htr 0 3 4 (by decide) (by decide) with h302 | h302
        · rcases m.htr 0 3 5 (by decide) (by decide) with h303 | h303
          · rcases m.htr 1 2 3 (by decide) (by decide) with h304 | h304
            · rcases m.htr 1 2 4 (by decide) (by decide) with h305 | h305
              · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                · linarith only [h0, h300, h306, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h300, h302, h306, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h0, h305, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h300, h301, h303, h304, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
          · linarith only [h302, h303, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h312 | h312
          · linarith only [h302, h312, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h314 | h314
            · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
              · rcases m.htr 1 3 4 (by decide) (by decide) with h316 | h316
                · linarith only [h300, h302, h316, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h318 | h318
                  · linarith only [h0, h300, h312, h318, hc12, hlam, hphi, ht01, u0ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h320 | h320
                    · linarith only [h302, h320, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                      · linarith only [h0, h300, h312, h314, h322, hc12, hlam, hphi, ht01, u0ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h324 | h324
                        · rcases h3bigk with h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c | h325c
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h312, h314, h324, hc34, hlam, hphi, ht23, p325_1, u2ehi2]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h312, h324, hc34, hlam, hphi, ht23, p325_1, u2ehi2]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h302, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h312, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h300, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h0, h300, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p325_1, u2ehi2]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h316, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h318, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h301, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h314, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h320, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h322, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hc34, hlam, hphi, p325_1, u3ehi0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hc34, hlam, hphi, p325_1, u3ehi1]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hc34, hlam, hphi, ht23, p325_1, u2ehi2]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hc34, hlam, hphi, p325_1, u3ehi4]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p325_1, u0ehi2]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h314, hc35, hlam, hphi, ht23, p325_1, u2ehi2]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hc35, hlam, hphi, ht23, p325_1, u2ehi2]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [h324, hlam, p325_0]
                          · have p325_0 := h325c.1
                            have p325_1 := h325c.2.1
                            have p325_2 := h325c.2.2.1
                            have p325_3 := h325c.2.2.2
                            linarith only [hlam, p325_0]
                        · linarith only [h0, h300, h302, h314, h324, hc12, hc45, hlam, hphi, ht01, ht23, ht34, u0ehi2, u2ehi2]
              · linarith only [h0, h300, h314, h315, hc24, hlam, hphi, u2ehi2]
            · linarith only [h0, h300, h314, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h0, h300, h301, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h355 | h355
      · rcases m.htr 0 3 4 (by decide) (by decide) with h356 | h356
        · rcases m.htr 0 3 5 (by decide) (by decide) with h357 | h357
          · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
            · rcases m.htr 1 2 4 (by decide) (by decide) with h359 | h359
              · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
                · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h363 | h363
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h364 | h364
                        · rcases h3bigk with h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c | h365c
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h300, hlam, p365_1]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h362, h364, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p365_1, u3ehi4]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            rcases p365_3 (m.d 0 3) (by simp) with h369 | h369
                            · rcases p365_3 (m.d 1 3) (by simp) with h370 | h370
                              · rcases p365_3 (m.d 2 3) (by simp) with h371 | h371
                                · linarith only [h355, h371, hlam]
                                · linarith only [h362, h371, hlam]
                              · linarith only [h360, h370, hlam]
                            · linarith only [h369, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            rcases p365_3 (m.d 0 3) (by simp) with h376 | h376
                            · rcases p365_3 (m.d 1 3) (by simp) with h377 | h377
                              · rcases p365_3 (m.d 2 3) (by simp) with h378 | h378
                                · linarith only [h355, h378, hlam]
                                · linarith only [h363, h378, hlam]
                              · linarith only [h361, h377, hlam]
                            · linarith only [h376, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [hc13, hlam, hphi, ht01, p365_1, u0ehi2]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h358, h362, h364, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p365_1, u3ehi4]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            rcases p365_3 (m.d 0 3) (by simp) with h386 | h386
                            · linarith only [h300, h386, hlam]
                            · linarith only [h356, h386, hlam]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            rcases p365_3 (m.d 0 3) (by simp) with h389 | h389
                            · linarith only [h300, h389, hlam]
                            · linarith only [h357, h389, hlam]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h355, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h358, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h355, h364, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p365_1, u3ehi4]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h0, h355, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p365_1, u3ehi4]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h356, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h360, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h362, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [hc34, hlam, hphi, p365_1, u3ehi4]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h357, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h361, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h363, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [h364, hlam, p365_0]
                          · have p365_0 := h365c.1
                            have p365_1 := h365c.2.1
                            have p365_2 := h365c.2.2.1
                            have p365_3 := h365c.2.2.2
                            linarith only [hlam, p365_0]
                        · rcases h3bigk with h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c | h407c
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h300, hlam, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h363, h364, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            rcases p407_3 (m.d 0 3) (by simp) with h411 | h411
                            · rcases p407_3 (m.d 1 3) (by simp) with h412 | h412
                              · rcases p407_3 (m.d 2 3) (by simp) with h413 | h413
                                · linarith only [h355, h413, hlam]
                                · linarith only [h362, h413, hlam]
                              · linarith only [h360, h412, hlam]
                            · linarith only [h411, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            rcases p407_3 (m.d 0 3) (by simp) with h418 | h418
                            · rcases p407_3 (m.d 1 3) (by simp) with h419 | h419
                              · rcases p407_3 (m.d 2 3) (by simp) with h420 | h420
                                · linarith only [h355, h420, hlam]
                                · linarith only [h363, h420, hlam]
                              · linarith only [h361, h419, hlam]
                            · linarith only [h418, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h358, hc12, hlam, hphi, ht01, p407_1, u0ehi2]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h358, h363, h364, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            rcases p407_3 (m.d 0 3) (by simp) with h428 | h428
                            · linarith only [h300, h428, hlam]
                            · linarith only [h356, h428, hlam]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            rcases p407_3 (m.d 0 3) (by simp) with h431 | h431
                            · linarith only [h300, h431, hlam]
                            · linarith only [h357, h431, hlam]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h355, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h358, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h355, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h0, h355, h364, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h356, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h360, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h362, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h364, hlam, p407_1]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h357, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h361, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [h363, hlam, p407_0]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hc35, hlam, hphi, p407_1, u3ehi3]
                          · have p407_0 := h407c.1
                            have p407_1 := h407c.2.1
                            have p407_2 := h407c.2.2.1
                            have p407_3 := h407c.2.2.2
                            linarith only [hlam, p407_0]
                      · linarith only [h300, h357, h358, h362, h363, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h450 | h450
                      · linarith only [h362, h450, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h452 | h452
                        · rcases h3bigk with h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c | h453c
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h300, hlam, p453_1]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            rcases p453_3 (m.d 0 3) (by simp) with h456 | h456
                            · rcases p453_3 (m.d 1 3) (by simp) with h457 | h457
                              · rcases p453_3 (m.d 2 3) (by simp) with h458 | h458
                                · linarith only [h355, h458, hlam]
                                · rcases p453_3 (m.d 3 4) (by simp) with h460 | h460
                                  · linarith only [h356, h460, hlam]
                                  · linarith only [h362, h460, hlam]
                              · linarith only [h358, h457, hlam]
                            · linarith only [h355, h456, hlam]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h300, h358, h450, h452, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p453_1, u3ehi2]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h300, h358, h450, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi2]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h358, hc12, hlam, hphi, ht01, p453_1, u0ehi2]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            rcases p453_3 (m.d 0 3) (by simp) with h469 | h469
                            · linarith only [h300, h469, hlam]
                            · linarith only [h355, h469, hlam]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h358, h450, h452, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi2]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h358, h450, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi2]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h355, hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h358, hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h362, hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h450, hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h356, hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h360, hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h356, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi2]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h300, h356, h358, h450, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p453_1, u2ehi2]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h357, hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h361, hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [hc35, hlam, hphi, ht23, p453_1, u2ehi2]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [h452, hlam, p453_0]
                          · have p453_0 := h453c.1
                            have p453_1 := h453c.2.1
                            have p453_2 := h453c.2.2.1
                            have p453_3 := h453c.2.2.2
                            linarith only [hlam, p453_0]
                        · linarith only [h362, h452, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h300, h357, h361, hlam]
                · linarith only [h300, h357, h360, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h359, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h355, h358, hc02, hlam, hphi, u0ehi0]
          · linarith only [h356, h357, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h495 | h495
          · linarith only [h356, h495, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h497 | h497
            · rcases m.htr 1 2 4 (by decide) (by decide) with h498 | h498
              · rcases m.htr 1 3 4 (by decide) (by decide) with h499 | h499
                · linarith only [h356, h499, hc13, hlam, hphi, ht01, u0ehi2]
                · linarith only [h300, h499, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
              · linarith only [h0, h498, hc24, hlam, hphi, ht01, ht12, u0ehi0]
            · linarith only [h0, h355, h497, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h504 | h504
        · rcases m.htr 0 3 5 (by decide) (by decide) with h505 | h505
          · rcases m.htr 1 2 3 (by decide) (by decide) with h506 | h506
            · linarith only [h0, h355, h506, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h506, hc23, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h504, h505, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h510 | h510
          · linarith only [h504, h510, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
            · linarith only [h0, h355, h512, hc12, hlam, hphi, ht01, u0ehi0]
            · linarith only [h0, h512, hc23, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
