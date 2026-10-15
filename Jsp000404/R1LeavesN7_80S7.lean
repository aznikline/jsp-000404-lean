import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_I_L_R_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h1ehi := hb1.1
  have h3ehi := hb3.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h10, h11, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                        · linarith only [h10, h14, hc23, hlam, hphi, ht12, u1ehi2]
                        · rcases h0bigk with h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c | h16c
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h4, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h6, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi4]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h6, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi3]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi4]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h1, hlam, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h4, hlam, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h10, h6, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi2]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi4]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h2, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h5, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h6, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p16_1, u1ehi4]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h3, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h4, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p16_1, u3ehi0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h7, hlam, p16_0]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [h8, hlam, p16_1]
                          · have p16_0 := h16c.1
                            have p16_1 := h16c.2.1
                            have p16_2 := h16c.2.2.1
                            have p16_3 := h16c.2.2.2
                            linarith only [hlam, p16_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h42 | h42
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                        · rcases h0bigk with h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c | h44c
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h3, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi4]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi4]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h4, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h3, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi4]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi4]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h1, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h4, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h3, h8, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi4]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h0, h3, h4, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi4]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h2, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h5, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h6, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h3, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p44_1, u1ehi4]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h3, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h4, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p44_1, u3ehi0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h7, hlam, p44_0]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [h8, hlam, p44_1]
                          · have p44_0 := h44c.1
                            have p44_1 := h44c.2.1
                            have p44_2 := h44c.2.2.1
                            have p44_3 := h44c.2.2.2
                            linarith only [hlam, p44_0]
                        · linarith only [h42, h43, h9, hc13, hlam, hphi, u1ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h71 | h71
                        · linarith only [h42, h71, h9, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h4, h6, h71, h9, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                        · linarith only [h0, h74, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1, h75, h76, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h6, h75, h8, hc45, hlam, hphi, ht34, u3ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h80 | h80
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                        · rcases h0bigk with h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c | h82c
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p82_1, u3ehi0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p82_1, u3ehi0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p82_1, u1ehi3]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p82_1, u3ehi4]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h1, h80, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p82_1, u3ehi3]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p82_1, u1ehi3]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h2, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p82_1, u1ehi3]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h1, hlam, p82_1]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h4, hlam, p82_1]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h2, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p82_1, u1ehi3]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h0, h2, h4, h8, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p82_1, u1ehi3]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h2, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h5, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h6, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h8, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h3, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h4, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p82_1, u3ehi0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h7, hlam, p82_0]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [h2, h7, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p82_1, u1ehi3]
                          · have p82_0 := h82c.1
                            have p82_1 := h82c.2.1
                            have p82_2 := h82c.2.2.1
                            have p82_3 := h82c.2.2.2
                            linarith only [hlam, p82_0]
                        · linarith only [h74, h80, h81, hc13, hlam, hphi, u1ehi1]
                      · linarith only [h6, h8, h80, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h111 | h111
                · linarith only [h111, h6, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h113 | h113
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h114 | h114
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h115 | h115
                      · linarith only [h1, h115, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                        · linarith only [h1, h114, h117, h6, hc12, hlam, hphi, u1ehi2]
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
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p119_1, u1ehi1]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p119_1, u1ehi2]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h1, h111, h113, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p119_1, u1ehi2]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h1, h111, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p119_1, u1ehi2]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h0, hlam, p119_0]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [hlam, p119_0]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p119_1, u1ehi2]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h0, h1, h111, h113, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p119_1, u1ehi2]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h0, h1, h111, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p119_1, u1ehi2]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h1, hlam, p119_1]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h4, hlam, p119_1]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [hlam, p119_0]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h6, hlam, p119_1]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h111, hlam, p119_1]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h2, hlam, p119_0]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h5, hlam, p119_0]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p119_1, u1ehi2]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [hlam, p119_0]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h1, h111, h6, hc34, hlam, hphi, ht12, ht23, p119_1, u1ehi2]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h3, hlam, p119_0]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h5, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p119_1]
                          · have p119_0 := h119c.1
                            have p119_1 := h119c.2.1
                            have p119_2 := h119c.2.2.1
                            have p119_3 := h119c.2.2.2
                            linarith only [h1, h111, hc35, hlam, hphi, ht12, ht23, p119_1, u1ehi2]
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
                    · linarith only [h114, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h146 | h146
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h147 | h147
                      · linarith only [h1, h113, h147, h6, hc45, hlam, hphi, ht34, u3ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h149 | h149
                        · linarith only [h146, h149, h6, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases h0bigk with h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c | h151c
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [hlam, p151_0]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p151_1, u1ehi1]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p151_1, u1ehi2]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h147, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p151_1, u1ehi2]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p151_1, u1ehi4]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h0, hlam, p151_0]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [hlam, p151_0]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h1, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p151_1, u1ehi2]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h0, h147, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p151_1, u1ehi2]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h0, h113, h147, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p151_1, u1ehi2]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h1, hlam, p151_1]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h4, hlam, p151_1]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [hlam, p151_0]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h6, hlam, p151_1]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h111, hlam, p151_1]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h2, hlam, p151_0]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h5, hlam, p151_0]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h1, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p151_1, u1ehi2]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [hlam, p151_0]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h113, hlam, p151_0]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h3, hlam, p151_0]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h113, hc02, hc45, hlam, hphi, ht23, ht34, p151_1]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h1, h113, hc45, hlam, hphi, ht12, ht23, ht34, p151_1, u1ehi2]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [h113, hc04, hc45, hlam, hphi, p151_1]
                          · have p151_0 := h151c.1
                            have p151_1 := h151c.2.1
                            have p151_2 := h151c.2.2.1
                            have p151_3 := h151c.2.2.2
                            linarith only [hlam, p151_0]
                    · linarith only [h146, h4, h6, hc34, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h178 | h178
              · linarith only [h178, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h180 | h180
                · linarith only [h178, h180, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h182 | h182
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
                      · linarith only [h1, h178, h184, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                        · linarith only [h0, h1, h178, h183, h186, h5, hc24, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h0, h183, h186, h5, hc34, hlam, hphi, u3ehi2]
                    · linarith only [h183, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h182, h4, h5, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h191 | h191
            · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
              · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
                · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                    · linarith only [h0, h191, h195, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                        · rcases h0bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h191, h198, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1, u3ehi3]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h191, h198, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1, u3ehi3]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h191, h194, h198, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p199_1, u1ehi4, u3ehi3]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h191, h198, h3, h4, hc01, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p199_1, u1ehi4, u3ehi3]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h0, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h4, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h194, h3, h4, hc23, hlam, hphi, ht12, p199_1, u1ehi4]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h3, h4, hc23, hlam, hphi, ht12, p199_1, u1ehi4]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h1, hlam, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h191, h198, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1, u3ehi3]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h194, h3, h4, hc23, hlam, hphi, ht12, p199_1, u1ehi4]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h3, h4, hc23, hlam, hphi, ht12, p199_1, u1ehi4]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h2, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h191, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h192, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h191, h198, h3, h4, hc04, hc23, hlam, hphi, ht0b, ht12, ht34, ht45, ht5b, p199_1, u1ehi4, u3ehi3]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h3, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h191, h198, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p199_1, u3ehi3]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h193, hlam, p199_0]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [h194, hlam, p199_1]
                          · have p199_0 := h199c.1
                            have p199_1 := h199c.2.1
                            have p199_2 := h199c.2.2.1
                            have p199_3 := h199c.2.2.2
                            linarith only [hlam, p199_0]
                        · linarith only [h191, h197, h198, h4, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h192, h195, h197, h4, hc23, hlam, hphi, ht12, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h227 | h227
                    · linarith only [h0, h227, h4, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h229 | h229
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                        · rcases h0bigk with h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c | h231c
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h191, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p231_1, u3ehi0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h194, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p231_1, u1ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h0, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h4, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h2, h4, hc23, hlam, hphi, ht12, p231_1, u1ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h194, h2, h4, hc23, hlam, hphi, ht12, p231_1, u1ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h1, hlam, p231_1]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h191, h230, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p231_1, u3ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h2, h4, hc23, hlam, hphi, ht12, p231_1, u1ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h194, h2, h4, hc23, hlam, hphi, ht12, p231_1, u1ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h2, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h191, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h192, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h194, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h3, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h191, h230, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p231_1, u3ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h193, hlam, p231_0]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [h191, h194, h2, h230, h4, hc23, hc45, hlam, hphi, ht12, ht34, p231_1, u1ehi3, u3ehi3]
                          · have p231_0 := h231c.1
                            have p231_1 := h231c.2.1
                            have p231_2 := h231c.2.2.1
                            have p231_3 := h231c.2.2.2
                            linarith only [hlam, p231_0]
                        · linarith only [h191, h229, h230, h4, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h192, h227, h229, h4, hc23, hlam, hphi, ht12, u1ehi1]
                · linarith only [h192, h193, hc35, hlam, hphi, u3ehi3]
              · linarith only [h191, h192, h4, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h261 | h261
              · rcases m.htr 0 3 5 (by decide) (by decide) with h262 | h262
                · rcases m.htr 0 4 5 (by decide) (by decide) with h263 | h263
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h264, h4, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h266 | h266
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                        · rcases h0bigk with h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c | h268c
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p268_1, u1ehi1]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h1, h266, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p268_1, u3ehi3]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h263, h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p268_1, u1ehi4]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p268_1, u1ehi4]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h0, hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h4, hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h191, hlam, p268_1]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h3, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p268_1, u1ehi4]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h1, hlam, p268_1]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p268_1, u1ehi1]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h263, h3, h4, hc23, hlam, hphi, ht12, p268_1, u1ehi4]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h3, h4, hc23, hlam, hphi, ht12, p268_1, u1ehi4]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h2, hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p268_1, u1ehi1]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h261, hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h191, h267, h3, hc23, hlam, hphi, ht12, p268_1, u1ehi4]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h3, hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h0, hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p268_1, u1ehi1]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h262, hlam, p268_0]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [h263, hlam, p268_1]
                          · have p268_0 := h268c.1
                            have p268_1 := h268c.2.1
                            have p268_2 := h268c.2.2.1
                            have p268_3 := h268c.2.2.2
                            linarith only [hlam, p268_0]
                        · linarith only [h262, h266, h267, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h261, h266, h4, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                    · linarith only [h0, h296, h4, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h298 | h298
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h299 | h299
                        · rcases h0bigk with h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p300_1, u1ehi1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p300_1, u3ehi0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p300_1, u1ehi3]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p300_1, u1ehi4]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h0, hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h4, hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h191, hlam, p300_1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h191, h263, hlam, p300_1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h1, hlam, p300_1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h0, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p300_1, u1ehi1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h0, h191, h4, hc23, hlam, hphi, ht12, p300_1, u1ehi1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h0, h191, h263, h4, hc23, hlam, hphi, ht12, p300_1, u1ehi1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h2, hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h0, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p300_1, u1ehi1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h261, hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h263, hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h3, hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h0, h263, hc45, hlam, hphi, ht12, ht23, ht34, p300_1, u1ehi1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h262, hlam, p300_0]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [h263, hc04, hc45, hlam, hphi, p300_1]
                          · have p300_0 := h300c.1
                            have p300_1 := h300c.2.1
                            have p300_2 := h300c.2.2.1
                            have p300_3 := h300c.2.2.2
                            linarith only [hlam, p300_0]
                        · linarith only [h1, h298, h299, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · linarith only [h261, h298, h4, hc23, hlam, hphi, ht12, u1ehi2]
                · linarith only [h261, h262, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h329 | h329
                · linarith only [h261, h329, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h331 | h331
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h332 | h332
                    · linarith only [h0, h332, h4, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h334 | h334
                      · linarith only [h0, h261, h334, h4, hc13, hlam, hphi, u1ehi1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h336 | h336
                        · linarith only [h0, h261, h336, h4, hc23, hlam, hphi, ht12, u1ehi1]
                        · linarith only [h0, h336, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
                    · linarith only [h0, h339, h4, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h341 | h341
                      · linarith only [h1, h261, h341, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h343 | h343
                        · linarith only [h1, h261, h343, hc23, hlam, hphi, ht12, u1ehi2]
                        · linarith only [h0, h343, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h349 | h349
    · linarith only [h0, h349, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h351 | h351
      · linarith only [h0, h351, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h353 | h353
        · linarith only [h0, h353, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h355 | h355
          · rcases m.htr 0 2 4 (by decide) (by decide) with h356 | h356
            · rcases m.htr 0 3 4 (by decide) (by decide) with h357 | h357
              · rcases m.htr 0 3 5 (by decide) (by decide) with h358 | h358
                · rcases m.htr 0 4 5 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h361 | h361
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h362 | h362
                        · rcases h0bigk with h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c | h363c
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
                            linarith only [h349, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h351, hlam, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h353, hlam, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h358, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p363_1, u3ehi4]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h353, h359, hc12, hlam, hphi, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h353, hc12, hlam, hphi, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h355, hlam, p363_1]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h349, h353, h359, h360, hc12, hlam, hphi, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h349, h353, h360, hc12, hlam, hphi, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h356, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h357, hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hlam, p363_0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h351, h353, h360, h361, hc12, hlam, hphi, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h0, h351, h359, h360, h361, hc12, hlam, hphi, p363_1, u1ehi0]
                          · have p363_0 := h363c.1
                            have p363_1 := h363c.2.1
                            have p363_2 := h363c.2.2.1
                            have p363_3 := h363c.2.2.2
                            linarith only [h358, hlam, p363_0]
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
                        · rcases h0bigk with h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c | h389c
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
                            linarith only [h349, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h351, hlam, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h353, hlam, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p389_1, u1ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p389_1, u3ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h0, h359, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h0, h353, hc12, hlam, hphi, p389_1, u1ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p389_1, u1ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h355, hlam, p389_1]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h349, h357, h360, h362, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p389_1, u3ehi2]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h349, h353, h360, hc12, hlam, hphi, p389_1, u1ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p389_1, u1ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h356, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h357, hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [hlam, p389_0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h351, h353, h360, h361, hc12, hlam, hphi, p389_1, u1ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h349, h357, h360, h362, hc05, hc12, hlam, hphi, ht0b, ht34, ht45, ht5b, p389_1, u1ehi0, u3ehi2]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h0, h351, h359, h360, h361, hc12, hlam, hphi, p389_1, u1ehi0]
                          · have p389_0 := h389c.1
                            have p389_1 := h389c.2.1
                            have p389_2 := h389c.2.2.1
                            have p389_3 := h389c.2.2.2
                            linarith only [h358, hlam, p389_0]
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
                      · linarith only [h349, h357, h361, hlam]
                    · linarith only [h0, h360, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h418 | h418
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h419 | h419
                        · rcases h0bigk with h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c | h420c
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [hlam, p420_0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h0, hlam, p420_1]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h349, hlam, p420_0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h351, hlam, p420_1]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h353, hlam, p420_1]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p420_1, u1ehi0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [hlam, p420_0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h0, h355, h419, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p420_1, u3ehi3]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h0, h351, hc12, hlam, hphi, p420_1, u1ehi0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h0, h353, hc12, hlam, hphi, p420_1, u1ehi0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p420_1, u1ehi0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h355, hlam, p420_1]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [hlam, p420_0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h0, h351, h355, hc12, hlam, hphi, p420_1, u1ehi0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h0, h353, h355, hc12, hlam, hphi, p420_1, u1ehi0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p420_1, u1ehi0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h356, hlam, p420_0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h357, hlam, p420_0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [hlam, p420_0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h359, hlam, p420_0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [hc05, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p420_1, u1ehi0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h359, hc02, hc45, hlam, hphi, ht23, ht34, p420_1]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h358, hlam, p420_0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [h351, h358, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p420_1, u1ehi0]
                          · have p420_0 := h420c.1
                            have p420_1 := h420c.2.1
                            have p420_2 := h420c.2.2.1
                            have p420_3 := h420c.2.2.2
                            linarith only [hlam, p420_0]
                        · linarith only [h357, h359, h419, hc45, hlam, hphi, ht34, u3ehi2]
                      · linarith only [h357, h359, h418, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h0, h417, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h357, h358, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h450 | h450
                · linarith only [h357, h450, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h453 | h453
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                      · linarith only [h349, h357, h454, hc13, hlam, hphi, u1ehi0]
                      · linarith only [h349, h454, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h0, h355, h453, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                      · linarith only [h349, h357, h459, hc13, hlam, hphi, u1ehi0]
                      · linarith only [h349, h459, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h355, h450, h458, hc35, hlam, hphi, ht12, ht23, u1ehi1]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h463 | h463
              · linarith only [h355, h356, h463, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h465 | h465
                · linarith only [h463, h465, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h469 | h469
                      · linarith only [h349, h463, h468, h469, hc12, hlam, hphi, u1ehi0]
                      · linarith only [h349, h469, hc34, hlam, hphi, ht12, ht23, u1ehi0]
                    · linarith only [h355, h356, h468, hc12, hc24, hlam, hphi]
                  · linarith only [h355, h356, h467, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h474 | h474
            · rcases m.htr 0 3 4 (by decide) (by decide) with h475 | h475
              · rcases m.htr 0 3 5 (by decide) (by decide) with h476 | h476
                · rcases m.htr 0 4 5 (by decide) (by decide) with h477 | h477
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h478 | h478
                    · linarith only [h0, h355, h478, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h478, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h481 | h481
                    · linarith only [h0, h355, h481, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h481, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h475, h476, hc35, hlam, hphi, u3ehi3]
              · linarith only [h355, h474, h475, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h486 | h486
              · rcases m.htr 0 3 5 (by decide) (by decide) with h487 | h487
                · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                    · linarith only [h0, h355, h489, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h489, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h492 | h492
                    · linarith only [h0, h355, h492, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h492, hc23, hlam, hphi, ht12, u1ehi0]
                · linarith only [h486, h487, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h496 | h496
                · linarith only [h486, h496, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h498 | h498
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
                    · linarith only [h0, h355, h499, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h499, hc23, hlam, hphi, ht12, u1ehi0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
                    · linarith only [h0, h355, h502, hc12, hlam, hphi, u1ehi0]
                    · linarith only [h0, h502, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
