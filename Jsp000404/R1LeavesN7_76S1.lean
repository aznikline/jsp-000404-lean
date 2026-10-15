import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_23_L_0_L_R_H_I (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0elo := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h4, h7, h9, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases h3bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h0, h4, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u0elo0, u2ehi3]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h0, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11_1, u0elo0, u2ehi3]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1, u0elo0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p11_1, u0elo0]
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
                        linarith only [h7, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p11_1, u2ehi3]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1, u0elo0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h0, hc35, hlam, hphi, ht0b, ht5b, p11_1, u0elo0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h1, hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h4, hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1, u0elo1]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h0, h4, hc35, hlam, hphi, ht0b, ht5b, p11_1, u0elo0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h2, hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h5, hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h7, hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h9, hlam, p11_1]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h3, hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h6, hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h8, hlam, p11_0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [h0, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p11_1, u0elo0]
                      · have p11_0 := h11c.1
                        have p11_1 := h11c.2.1
                        have p11_2 := h11c.2.2.1
                        have p11_3 := h11c.2.2.2
                        linarith only [hlam, p11_0]
                  · linarith only [h0, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · linarith only [h0, h2, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
              · linarith only [h0, h3, h5, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h0, h2, h4, h5, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
          · linarith only [h1, h4, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
          · rcases m.htr 1 3 4 (by decide) (by decide) with h43 | h43
            · rcases m.htr 1 3 5 (by decide) (by decide) with h44 | h44
              · linarith only [h0, h3, h44, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h46 | h46
                · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                  · linarith only [h0, h3, h42, h47, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                    · linarith only [h0, h42, h46, h49, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases h3bigk with h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h42, h46, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p51_1, u0elo2, u2ehi3]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h3, h46, h49, hc45, hlam, hphi, ht23, ht34, p51_1, u2ehi3]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h3, h49, hc34, hc45, hlam, hphi, p51_1]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h3, hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h0, hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h46, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p51_1, u2ehi3]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p51_1, u0elo0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h44, hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h1, hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h42, hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h42, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p51_1]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h47, hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h2, hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h43, hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h46, hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [hlam, p51_0]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h49, hlam, p51_1]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h49, hc03, hc45, hlam, hphi, ht34, p51_1]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h42, h49, hc45, hlam, hphi, ht23, ht34, p51_1, u2ehi2]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h46, h49, hc45, hlam, hphi, ht23, ht34, p51_1, u2ehi3]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [h49, hc34, hc45, hlam, hphi, p51_1]
                      · have p51_0 := h51c.1
                        have p51_1 := h51c.2.1
                        have p51_2 := h51c.2.2.1
                        have p51_3 := h51c.2.2.2
                        linarith only [hlam, p51_0]
                · linarith only [h2, h46, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
            · linarith only [h2, h3, h42, h43, hc35, hlam, hphi, ht23, u2ehi2]
          · linarith only [h1, h42, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h80 | h80
        · rcases m.htr 1 2 3 (by decide) (by decide) with h81 | h81
          · rcases m.htr 1 3 4 (by decide) (by decide) with h82 | h82
            · linarith only [h0, h2, h82, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h84 | h84
              · rcases m.htr 2 3 4 (by decide) (by decide) with h85 | h85
                · linarith only [h0, h2, h81, h85, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h87 | h87
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                    · rcases h3bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h81, h87, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p89_1, u0elo2, u2ehi4]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h2, h87, hc34, hlam, hphi, ht23, p89_1, u2ehi4]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h2, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h2, h88, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p89_1]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h0, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h87, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p89_1, u2ehi4]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h82, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h0, h88, hc45, hlam, hphi, ht0b, ht5b, p89_1, u0elo0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h1, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h81, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h85, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h81, h88, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p89_1]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [hc03, hc34, hlam, hphi, p89_1]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h81, h87, hc34, hlam, hphi, ht23, p89_1, u2ehi4]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h87, hc34, hlam, hphi, ht23, p89_1, u2ehi4]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        rcases p89_3 (m.d 0 3) (by simp) with h109 | h109
                        · linarith only [h109, h2, hlam]
                        · linarith only [h109, h80, hlam]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h80, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h84, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h87, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [h88, hlam, p89_0]
                      · have p89_0 := h89c.1
                        have p89_1 := h89c.2.1
                        have p89_2 := h89c.2.2.1
                        have p89_3 := h89c.2.2.2
                        linarith only [hlam, p89_0]
                    · linarith only [h0, h2, h81, h87, h88, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · linarith only [h2, h80, h87, hc23, hc34, hlam, hphi]
              · linarith only [h2, h80, h84, hc13, hc34, hlam, hphi]
          · linarith only [h1, h81, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h121 | h121
          · rcases m.htr 1 3 4 (by decide) (by decide) with h122 | h122
            · linarith only [h0, h122, h2, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h124 | h124
              · linarith only [h0, h124, h80, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h126 | h126
                · linarith only [h0, h121, h126, h2, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h128 | h128
                  · linarith only [h0, h121, h128, h80, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h130 | h130
                    · rcases h3bigk with h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c | h131c
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h121, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p131_1, u0elo2, u2ehi2]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h130, h80, hc34, hlam, hphi, ht23, p131_1, u2ehi2]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h2, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h80, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h0, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p131_1, u2ehi2]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h122, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h124, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h1, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h121, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h126, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h128, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hc03, hc34, hlam, hphi, p131_1]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hc13, hc34, hlam, hphi, p131_1]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hc34, hlam, hphi, ht23, p131_1, u2ehi2]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h0, h121, h80, hc34, hlam, hphi, ht23, p131_1, u2ehi2]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h0, h121, hc35, hlam, hphi, ht23, p131_1, u2ehi2]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h121, hc35, hlam, hphi, ht23, p131_1, u2ehi2]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hc35, hlam, hphi, ht23, p131_1, u2ehi2]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [h130, hlam, p131_0]
                      · have p131_0 := h131c.1
                        have p131_1 := h131c.2.1
                        have p131_2 := h131c.2.2.1
                        have p131_3 := h131c.2.2.2
                        linarith only [hlam, p131_0]
                    · linarith only [h0, h121, h130, h2, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h1, h121, h2, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h159 | h159
      · rcases m.htr 0 3 5 (by decide) (by decide) with h160 | h160
        · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
          · linarith only [h0, h1, h161, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h163 | h163
            · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
              · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h167 | h167
                    · linarith only [h0, h163, h167, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases h3bigk with h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c | h169c
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p169_1, u0elo2]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h1, hlam, p169_1]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1, u0elo0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h0, h167, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1, u0elo0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h0, hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h161, hlam, p169_1]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h0, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1, u0elo0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h0, h167, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1, u0elo0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h1, hc23, hlam, hphi, p169_1, u2ehi0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h161, hc23, hlam, hphi, p169_1, u2ehi1]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        rcases p169_3 (m.d 0 3) (by simp) with h183 | h183
                        · linarith only [h1, h183, hlam]
                        · linarith only [h159, h183, hlam]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        rcases p169_3 (m.d 0 3) (by simp) with h186 | h186
                        · linarith only [h1, h186, hlam]
                        · linarith only [h160, h186, hlam]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h159, hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h163, hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h165, hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h167, hlam, p169_1]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h160, hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h164, hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h166, hlam, p169_0]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [h160, hc34, hlam, hphi, ht0b, ht45, ht5b, p169_1, u0elo2]
                      · have p169_0 := h169c.1
                        have p169_1 := h169c.2.1
                        have p169_2 := h169c.2.2.1
                        have p169_3 := h169c.2.2.2
                        linarith only [hlam, p169_0]
                  · linarith only [h0, h164, h166, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi2]
                · linarith only [h1, h165, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h160, h161, h164, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
            · linarith only [h0, h159, h161, h163, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h203 | h203
          · linarith only [h0, h1, h203, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h205 | h205
            · rcases m.htr 1 3 5 (by decide) (by decide) with h206 | h206
              · linarith only [h0, h160, h206, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h208 | h208
                · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                  · linarith only [h0, h160, h203, h209, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h1, h209, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h0, h1, h205, h208, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
            · linarith only [h159, h160, h205, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h214 | h214
        · rcases m.htr 1 2 3 (by decide) (by decide) with h215 | h215
          · linarith only [h0, h1, h215, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h217 | h217
            · linarith only [h0, h159, h217, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h219 | h219
              · rcases m.htr 2 3 4 (by decide) (by decide) with h220 | h220
                · linarith only [h0, h159, h215, h220, hc23, hlam, hphi, u2ehi1]
                · linarith only [h1, h220, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h214, h215, h219, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h224 | h224
          · linarith only [h0, h1, h224, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h226 | h226
            · linarith only [h0, h159, h226, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h228 | h228
              · linarith only [h0, h214, h228, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                · linarith only [h0, h159, h224, h230, hc23, hlam, hphi, u2ehi1]
                · linarith only [h1, h230, hc34, hlam, hphi, ht23, u2ehi0]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h233 | h233
    · rcases m.htr 0 3 4 (by decide) (by decide) with h234 | h234
      · rcases m.htr 0 3 5 (by decide) (by decide) with h235 | h235
        · rcases m.htr 1 2 3 (by decide) (by decide) with h236 | h236
          · rcases m.htr 1 3 4 (by decide) (by decide) with h237 | h237
            · rcases m.htr 1 3 5 (by decide) (by decide) with h238 | h238
              · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                · rcases m.htr 2 3 5 (by decide) (by decide) with h240 | h240
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h241 | h241
                    · linarith only [h233, h239, h241, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases h3bigk with h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h0, hlam, p243_1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p243_1, u0elo2]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h233, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1, u0elo1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h233, h241, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1, u0elo1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h0, hc01, hc13, hlam, hphi, p243_1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h236, h239, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p243_1, u2ehi3]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        rcases p243_3 (m.d 0 3) (by simp) with h252 | h252
                        · linarith only [h0, h252, hlam]
                        · linarith only [h234, h252, hlam]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        rcases p243_3 (m.d 0 3) (by simp) with h255 | h255
                        · linarith only [h0, h255, hlam]
                        · linarith only [h235, h255, hlam]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h233, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h236, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h233, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1, u0elo2]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h233, h241, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1, u0elo1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h234, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h237, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h239, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h241, hlam, p243_1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h235, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h238, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h240, hlam, p243_0]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [h233, h235, hc34, hlam, hphi, ht0b, ht45, ht5b, p243_1, u0elo1]
                      · have p243_0 := h243c.1
                        have p243_1 := h243c.2.1
                        have p243_2 := h243c.2.2.1
                        have p243_3 := h243c.2.2.2
                        linarith only [hlam, p243_0]
                  · linarith only [h233, h235, h240, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
                · linarith only [h233, h234, h239, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi2]
              · linarith only [h0, h233, h235, h238, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h234, h237, hlam]
          · linarith only [h233, h236, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h278 | h278
          · rcases m.htr 1 3 4 (by decide) (by decide) with h279 | h279
            · rcases m.htr 1 3 5 (by decide) (by decide) with h280 | h280
              · rcases m.htr 2 3 4 (by decide) (by decide) with h281 | h281
                · rcases m.htr 2 3 5 (by decide) (by decide) with h282 | h282
                  · linarith only [h233, h235, h282, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h284 | h284
                    · linarith only [h233, h235, h278, h280, h281, h284, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
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
                        linarith only [h0, hlam, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h235, h278, h280, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h235, h278, h280, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h235, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h0, h278, hc01, hc12, hlam, hphi, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h278, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p286_1, u2ehi2]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        rcases p286_3 (m.d 0 3) (by simp) with h295 | h295
                        · linarith only [h0, h295, hlam]
                        · linarith only [h234, h295, hlam]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h233, h235, h278, h281, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p286_1, u2ehi3]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h233, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h278, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h233, hc34, hlam, hphi, ht0b, ht45, ht5b, p286_1, u0elo2]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h282, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h234, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h279, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h281, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h284, hlam, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hc03, hc35, hlam, hphi, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h280, hlam, p286_0]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h278, h280, h281, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p286_1, u2ehi3]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [h278, h280, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p286_1]
                      · have p286_0 := h286c.1
                        have p286_1 := h286c.2.1
                        have p286_2 := h286c.2.2.1
                        have p286_3 := h286c.2.2.2
                        linarith only [hlam, p286_0]
                · linarith only [h234, h235, h278, h280, h281, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h315 | h315
                · rcases m.htr 2 3 5 (by decide) (by decide) with h316 | h316
                  · linarith only [h0, h233, h280, h316, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h318 | h318
                    · linarith only [h233, h315, h318, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                    · rcases h3bigk with h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h0, hlam, p320_1]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p320_1, u0elo2]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h0, h280, h318, hc34, hc45, hlam, hphi, p320_1]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h235, hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h280, h318, hc03, hc45, hlam, hphi, ht34, p320_1]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h280, h318, hc45, hlam, hphi, ht23, ht34, p320_1, u2ehi2]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h280, h318, hc34, hc45, hlam, hphi, p320_1]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h280, hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h233, hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h278, hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h233, hc34, hlam, hphi, ht0b, ht45, ht5b, p320_1, u0elo2]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h316, hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h234, hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h279, hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h315, hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [hlam, p320_0]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h318, hlam, p320_1]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h318, hc03, hc45, hlam, hphi, ht34, p320_1]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h318, hc13, hc45, hlam, hphi, ht34, p320_1]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h315, h318, hc45, hlam, hphi, ht23, ht34, p320_1, u2ehi3]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [h318, hc34, hc45, hlam, hphi, p320_1]
                      · have p320_0 := h320c.1
                        have p320_1 := h320c.2.1
                        have p320_2 := h320c.2.2.1
                        have p320_3 := h320c.2.2.2
                        linarith only [hlam, p320_0]
                · linarith only [h234, h315, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
            · linarith only [h0, h234, h279, hlam]
          · linarith only [h233, h278, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h349 | h349
        · rcases m.htr 1 2 3 (by decide) (by decide) with h350 | h350
          · rcases m.htr 1 3 4 (by decide) (by decide) with h351 | h351
            · rcases m.htr 1 3 5 (by decide) (by decide) with h352 | h352
              · rcases m.htr 2 3 4 (by decide) (by decide) with h353 | h353
                · linarith only [h233, h234, h353, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h356 | h356
                    · rcases h3bigk with h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c | h357c
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h0, hlam, p357_1]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h234, h350, h351, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p357_1]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h234, hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h234, h350, h351, h356, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p357_1]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h0, h350, hc01, hc12, hlam, hphi, p357_1]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h350, h355, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p357_1, u2ehi4]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h233, h234, h350, h355, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p357_1, u2ehi4]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        rcases p357_3 (m.d 0 3) (by simp) with h367 | h367
                        · linarith only [h0, h367, hlam]
                        · linarith only [h349, h367, hlam]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h233, hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h350, hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h353, hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h233, h356, hc45, hlam, hphi, ht0b, ht5b, p357_1, u0elo2]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h233, hc23, hc34, hlam, hphi, p357_1]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h351, hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h350, h351, h355, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p357_1, u2ehi4]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h350, h351, h356, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p357_1]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h349, hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h352, hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h355, hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [h356, hlam, p357_0]
                      · have p357_0 := h357c.1
                        have p357_1 := h357c.2.1
                        have p357_2 := h357c.2.2.1
                        have p357_3 := h357c.2.2.2
                        linarith only [hlam, p357_0]
                    · linarith only [h233, h234, h355, h356, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · linarith only [h349, h355, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi2]
              · linarith only [h234, h349, h351, h352, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h388 | h388
              · rcases m.htr 2 3 4 (by decide) (by decide) with h389 | h389
                · linarith only [h0, h351, h389, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h391 | h391
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h392 | h392
                    · rcases h3bigk with h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h0, hlam, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p393_1, u0elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h234, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h0, h351, h392, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h351, hc03, hc34, hlam, hphi, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h351, hc34, hlam, hphi, ht23, p393_1, u2ehi2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h351, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h351, h392, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h233, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h350, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h389, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h233, h392, hc45, hlam, hphi, ht0b, ht5b, p393_1, u0elo2]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hc03, hc34, hlam, hphi, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hc13, hc34, hlam, hphi, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hc23, hc34, hlam, hphi, p393_1]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        rcases p393_3 (m.d 0 3) (by simp) with h413 | h413
                        · linarith only [h234, h413, hlam]
                        · linarith only [h349, h413, hlam]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h349, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h388, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h391, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [h392, hlam, p393_0]
                      · have p393_0 := h393c.1
                        have p393_1 := h393c.2.1
                        have p393_2 := h393c.2.2.1
                        have p393_3 := h393c.2.2.2
                        linarith only [hlam, p393_0]
                    · linarith only [h233, h234, h391, h392, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                  · linarith only [h0, h349, h351, h391, hc23, hc34, hlam, hphi]
              · linarith only [h0, h349, h388, hlam]
          · linarith only [h233, h350, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
          · rcases m.htr 1 3 4 (by decide) (by decide) with h426 | h426
            · rcases m.htr 1 3 5 (by decide) (by decide) with h427 | h427
              · rcases m.htr 2 3 4 (by decide) (by decide) with h428 | h428
                · linarith only [h233, h234, h428, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h430 | h430
                  · linarith only [h233, h349, h430, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h432 | h432
                    · rcases h3bigk with h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c | h433c
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h0, hlam, p433_1]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h349, h425, h426, h432, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p433_1]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h234, hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h349, hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h0, h425, hc01, hc12, hlam, hphi, p433_1]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h425, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p433_1, u2ehi2]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h425, h432, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p433_1]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h233, h349, h425, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p433_1, u2ehi2]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h233, hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h425, hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h428, hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h430, hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h233, hc34, hlam, hphi, ht23, p433_1, u2ehi2]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h426, hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h425, h426, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p433_1, u2ehi2]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h233, h349, h425, h426, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p433_1, u2ehi2]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h233, h427, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p433_1, u2ehi2]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h427, hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h425, h427, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p433_1, u2ehi2]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [h432, hlam, p433_0]
                      · have p433_0 := h433c.1
                        have p433_1 := h433c.2.1
                        have p433_2 := h433c.2.2.1
                        have p433_3 := h433c.2.2.2
                        linarith only [hlam, p433_0]
                    · linarith only [h233, h234, h432, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h233, h234, h426, h427, hc35, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h461 | h461
              · linarith only [h233, h349, h426, h461, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h463 | h463
                · linarith only [h0, h233, h426, h463, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h465 | h465
                  · linarith only [h0, h233, h461, h465, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h467 | h467
                    · rcases h3bigk with h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c | h468c
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h0, hlam, p468_1]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p468_1, u0elo2, u2ehi2]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h234, hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h349, hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h461, h467, hc03, hc34, hlam, hphi, p468_1]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h461, h467, hc34, hlam, hphi, ht23, p468_1, u2ehi2]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h426, hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h461, hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h233, hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h425, hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h463, hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h465, hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h233, hc34, hlam, hphi, ht23, p468_1, u2ehi2]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [hc13, hc34, hlam, hphi, p468_1]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [hc34, hlam, hphi, ht23, p468_1, u2ehi2]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h233, h349, hc34, hlam, hphi, ht23, p468_1, u2ehi2]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h233, hc35, hlam, hphi, ht23, p468_1, u2ehi2]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h0, h233, hc35, hlam, hphi, ht23, p468_1, u2ehi2]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [hc35, hlam, hphi, ht23, p468_1, u2ehi2]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [h467, hlam, p468_0]
                      · have p468_0 := h468c.1
                        have p468_1 := h468c.2.1
                        have p468_2 := h468c.2.2.1
                        have p468_3 := h468c.2.2.2
                        linarith only [hlam, p468_0]
                    · linarith only [h233, h234, h467, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h233, h425, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1, u2ehi1]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h496 | h496
      · rcases m.htr 0 3 5 (by decide) (by decide) with h497 | h497
        · rcases m.htr 1 2 3 (by decide) (by decide) with h498 | h498
          · rcases m.htr 1 3 4 (by decide) (by decide) with h499 | h499
            · rcases m.htr 1 3 5 (by decide) (by decide) with h500 | h500
              · rcases m.htr 2 3 4 (by decide) (by decide) with h501 | h501
                · rcases m.htr 2 3 5 (by decide) (by decide) with h502 | h502
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h503 | h503
                    · rcases h3bigk with h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c | h504c
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h0, hlam, p504_1]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h233, hlam, p504_1]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p504_1, u0elo2]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h233, h498, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p504_1]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h0, hc01, hc13, hlam, hphi, p504_1]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h498, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p504_1, u2ehi2]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h498, h503, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p504_1]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        rcases p504_3 (m.d 0 3) (by simp) with h514 | h514
                        · linarith only [h0, h514, hlam]
                        · linarith only [h497, h514, hlam]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h496, h503, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p504_1]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h498, hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h498, h503, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p504_1]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h498, h503, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p504_1]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h496, hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h499, hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h501, hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h496, h503, hc45, hlam, hphi, ht0b, ht5b, p504_1, u0elo2]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h497, hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h500, hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h502, hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [h503, hlam, p504_0]
                      · have p504_0 := h504c.1
                        have p504_1 := h504c.2.1
                        have p504_2 := h504c.2.2.1
                        have p504_3 := h504c.2.2.2
                        linarith only [hlam, p504_0]
                    · rcases h3bigk with h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c | h532c
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h0, hlam, p532_1]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h233, hlam, p532_1]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h233, h498, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p532_1]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h233, h498, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p532_1]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h0, h498, hc01, hc12, hlam, hphi, p532_1]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h498, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p532_1, u2ehi2]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        rcases p532_3 (m.d 0 3) (by simp) with h541 | h541
                        · linarith only [h0, h541, hlam]
                        · linarith only [h496, h541, hlam]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        rcases p532_3 (m.d 0 3) (by simp) with h544 | h544
                        · linarith only [h0, h544, hlam]
                        · linarith only [h497, h544, hlam]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h233, hc23, hlam, hphi, p532_1, u2ehi0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h498, hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h498, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p532_1]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h498, h503, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p532_1]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h496, hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h499, hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h501, hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h503, hlam, p532_1]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h497, hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h500, hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h502, hlam, p532_0]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [h497, hc34, hlam, hphi, ht0b, ht45, ht5b, p532_1, u0elo2]
                      · have p532_0 := h532c.1
                        have p532_1 := h532c.2.1
                        have p532_2 := h532c.2.2.1
                        have p532_3 := h532c.2.2.2
                        linarith only [hlam, p532_0]
                  · linarith only [h233, h497, h502, hlam]
                · linarith only [h233, h501, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h0, h497, h500, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h233, h496, h498, h499, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h566 | h566
            · rcases m.htr 1 3 5 (by decide) (by decide) with h567 | h567
              · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                · rcases m.htr 2 3 5 (by decide) (by decide) with h569 | h569
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h570 | h570
                    · rcases h3bigk with h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c | h571c
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h0, hlam, p571_1]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h233, hlam, p571_1]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p571_1, u0elo2]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [hc35, hlam, hphi, ht0b, ht5b, p571_1, u0elo2]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h0, h498, hc01, hc23, hlam, hphi, ht12, p571_1]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h498, hlam, p571_1]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h498, h570, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p571_1]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        rcases p571_3 (m.d 0 3) (by simp) with h581 | h581
                        · linarith only [h0, h581, hlam]
                        · linarith only [h497, h581, hlam]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h496, h570, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p571_1]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p571_1]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h570, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p571_1]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        rcases p571_3 (m.d 0 3) (by simp) with h588 | h588
                        · linarith only [h233, h588, hlam]
                        · linarith only [h497, h588, hlam]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h496, hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h566, hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h568, hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h496, h570, hc45, hlam, hphi, ht0b, ht5b, p571_1, u0elo2]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h497, hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h567, hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h569, hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [h570, hlam, p571_0]
                      · have p571_0 := h571c.1
                        have p571_1 := h571c.2.1
                        have p571_2 := h571c.2.2.1
                        have p571_3 := h571c.2.2.2
                        linarith only [hlam, p571_0]
                    · rcases h3bigk with h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c | h601c
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, hlam, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h233, hlam, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p601_1, u0elo2]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hc35, hlam, hphi, ht0b, ht5b, p601_1, u0elo2]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, hc01, hc13, hlam, hphi, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h498, hlam, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        rcases p601_3 (m.d 0 3) (by simp) with h610 | h610
                        · linarith only [h0, h610, hlam]
                        · linarith only [h496, h610, hlam]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        rcases p601_3 (m.d 0 3) (by simp) with h613 | h613
                        · linarith only [h0, h613, hlam]
                        · linarith only [h497, h613, hlam]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h233, hc23, hlam, hphi, p601_1, u2ehi0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h0, hc01, hc23, hlam, hphi, ht12, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        rcases p601_3 (m.d 0 3) (by simp) with h619 | h619
                        · linarith only [h233, h619, hlam]
                        · linarith only [h496, h619, hlam]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        rcases p601_3 (m.d 0 3) (by simp) with h622 | h622
                        · linarith only [h233, h622, hlam]
                        · linarith only [h497, h622, hlam]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h496, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h566, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h568, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h570, hlam, p601_1]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h497, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h567, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h569, hlam, p601_0]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [h497, hc34, hlam, hphi, ht0b, ht45, ht5b, p601_1, u0elo2]
                      · have p601_0 := h601c.1
                        have p601_1 := h601c.2.1
                        have p601_2 := h601c.2.2.1
                        have p601_3 := h601c.2.2.2
                        linarith only [hlam, p601_0]
                  · linarith only [h497, h498, h569, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi1]
                · linarith only [h233, h568, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h0, h497, h567, hlam]
            · linarith only [h0, h496, h566, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h639 | h639
          · rcases m.htr 1 3 4 (by decide) (by decide) with h640 | h640
            · rcases m.htr 1 3 5 (by decide) (by decide) with h641 | h641
              · rcases m.htr 2 3 4 (by decide) (by decide) with h642 | h642
                · rcases m.htr 2 3 5 (by decide) (by decide) with h643 | h643
                  · linarith only [h233, h497, h643, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h233, h639, h641, h643, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h233, h496, h497, h639, h641, h642, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h233, h639, h641, hc35, hlam, hphi, ht23, u2ehi0]
            · linarith only [h233, h496, h639, h640, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h649 | h649
            · rcases m.htr 1 3 5 (by decide) (by decide) with h650 | h650
              · linarith only [h233, h497, h639, h650, hc23, hlam, hphi, u2ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h652 | h652
                · rcases m.htr 2 3 5 (by decide) (by decide) with h653 | h653
                  · linarith only [h639, h650, h653, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h233, h653, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h233, h496, h652, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2, u2ehi0]
            · linarith only [h0, h496, h649, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h658 | h658
        · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
          · rcases m.htr 1 3 4 (by decide) (by decide) with h660 | h660
            · rcases m.htr 1 3 5 (by decide) (by decide) with h661 | h661
              · rcases m.htr 2 3 4 (by decide) (by decide) with h662 | h662
                · linarith only [h233, h496, h662, hc23, hlam, hphi, u2ehi0]
                · linarith only [h233, h659, h660, h662, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h496, h658, h660, h661, hlam]
            · linarith only [h233, h659, h660, hc34, hlam, hphi, ht23, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h667 | h667
            · linarith only [h233, h496, h659, h667, hc23, hlam, hphi, u2ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h669 | h669
              · rcases m.htr 2 3 4 (by decide) (by decide) with h670 | h670
                · linarith only [h659, h667, h670, hc23, hlam, hphi, u2ehi1]
                · linarith only [h233, h670, hc34, hlam, hphi, ht23, u2ehi0]
              · linarith only [h0, h658, h669, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h674 | h674
          · rcases m.htr 1 3 4 (by decide) (by decide) with h675 | h675
            · rcases m.htr 1 3 5 (by decide) (by decide) with h676 | h676
              · rcases m.htr 2 3 4 (by decide) (by decide) with h677 | h677
                · linarith only [h233, h496, h677, hc23, hlam, hphi, u2ehi0]
                · linarith only [h233, h675, h677, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
              · linarith only [h233, h496, h675, h676, hc35, hlam, hphi, ht23, u2ehi0]
            · linarith only [h233, h674, h675, hc34, hlam, hphi, ht23, u2ehi0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h682 | h682
            · linarith only [h233, h496, h674, h682, hc23, hlam, hphi, u2ehi0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h684 | h684
              · linarith only [h233, h658, h682, h684, hc34, hlam, hphi, ht23, u2ehi0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h686 | h686
                · linarith only [h674, h682, h686, hc23, hlam, hphi, u2ehi1]
                · linarith only [h233, h686, hc34, hlam, hphi, ht23, u2ehi0]

end R2N4
