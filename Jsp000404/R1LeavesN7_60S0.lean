import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3432000 in
theorem r1l7_11_13_25_L_0_L_R_H_I_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1elo := hb1.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
  · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
    · rcases m.htr 0 4 5 (by decide) (by decide) with h4 | h4
      · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
          · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                      · rcases h5bigk with h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c | h13c
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h0, h10, h5, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13_1, u1elo0, u3ehi4]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h0, h10, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13_1, u1elo0, u3ehi4]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13_1, u1elo0, u3ehi4]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p13_1, u1elo0]
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
                          linarith only [h10, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13_1, u1elo4, u3ehi4]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13_1, u1elo0, u3ehi4]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p13_1, u1elo0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h2, hlam, p13_1]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h5, hlam, p13_1]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p13_1, u3ehi4]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h0, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p13_1, u1elo0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h3, hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h7, hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h10, hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h3, hc03, hc45, hlam, hphi, ht0b, ht5b, p13_1]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h4, hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h8, hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h11, hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [h12, hlam, p13_0]
                        · have p13_0 := h13c.1
                          have p13_1 := h13c.2.1
                          have p13_2 := h13c.2.2.1
                          have p13_3 := h13c.2.2.2
                          linarith only [hlam, p13_0]
                      · linarith only [h12, h6, h8, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h11, h6, h8, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                  · linarith only [h10, h7, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
                · linarith only [h6, h9, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                    · linarith only [h1, h45, h6, h8, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h47 | h47
                      · linarith only [h47, h6, h8, hlam]
                      · rcases h5bigk with h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c | h49c
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p49_1, u1elo0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, h44, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p49_1, u1elo0, u3ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p49_1, u1elo0, u3ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, h8, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p49_1, u1elo0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h44, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p49_1, u1elo4, u3ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p49_1, u1elo0, u3ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h8, hlam, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h2, hlam, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h5, hlam, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p49_1, u3ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h45, hlam, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h3, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h7, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h44, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h47, hlam, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h4, hlam, p49_0]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h1, h4, h5, hc02, hc25, hlam, hphi, ht0b, ht5b, p49_1]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, h4, h44, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p49_1, u1elo0, u3ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [h0, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p49_1, u1elo0, u3ehi4]
                        · have p49_0 := h49c.1
                          have p49_1 := h49c.2.1
                          have p49_2 := h49c.2.2.1
                          have p49_3 := h49c.2.2.2
                          linarith only [hlam, p49_0]
                  · linarith only [h43, h44, hc35, hlam, hphi, u3ehi3]
                · linarith only [h43, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
            · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
            · linarith only [h6, h78, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
              · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                · rcases m.htr 2 3 5 (by decide) (by decide) with h82 | h82
                  · linarith only [h5, h78, h82, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1, u3ehi1]
                  · linarith only [h0, h3, h81, h82, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h85 | h85
                  · linarith only [h1, h78, h81, h85, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h87 | h87
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h88 | h88
                      · rcases h5bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h0, h78, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p89_1, u1elo0, u3ehi1]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo0]
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
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo4]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h78, hlam, p89_1]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h2, hlam, p89_1]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h5, hlam, p89_1]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h85, hlam, p89_1]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p89_1]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h3, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h3, h5, hc03, hc25, hlam, hphi, ht0b, ht5b, p89_1]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h0, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h0, h3, hc45, hlam, hphi, ht01, ht0b, ht5b, p89_1, u1elo0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h4, hlam, p89_0]
                        · have p89_0 := h89c.1
                          have p89_1 := h89c.2.1
                          have p89_2 := h89c.2.2.1
                          have p89_3 := h89c.2.2.2
                          linarith only [h80, hlam, p89_0]
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
                      · linarith only [h0, h4, h6, h88, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                    · linarith only [h80, h81, h87, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                  · linarith only [h0, h118, h5, h78, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · linarith only [h117, h118, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h121 | h121
                  · linarith only [h117, h121, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h123 | h123
                    · linarith only [h1, h123, h6, h80, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h125 | h125
                      · linarith only [h117, h123, h125, hc34, hlam, hphi, u3ehi2]
                      · linarith only [h0, h125, h4, h6, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h128 | h128
          · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
            · rcases m.htr 1 4 5 (by decide) (by decide) with h130 | h130
              · rcases m.htr 2 3 4 (by decide) (by decide) with h131 | h131
                · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h133 | h133
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h134 | h134
                      · rcases h5bigk with h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c | h135c
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p135_1, u1elo0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h0, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p135_1, u1elo0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p135_1, u1elo0, u3ehi4]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p135_1, u1elo0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h0, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h5, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p135_1, u1elo4, u3ehi4]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p135_1, u1elo0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h2, hlam, p135_1]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p135_1]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p135_1, u1elo0, u3ehi4]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h0, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p135_1, u1elo0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h3, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h129, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h132, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h129, hc45, hlam, hphi, ht01, ht0b, ht5b, p135_1, u1elo4]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h4, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h130, hlam, p135_0]
                        · have p135_0 := h135c.1
                          have p135_1 := h135c.2.1
                          have p135_2 := h135c.2.2.1
                          have p135_3 := h135c.2.2.2
                          linarith only [h133, hlam, p135_0]
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
                      · linarith only [h128, h130, h134, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                    · linarith only [h128, h130, h131, h133, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi3]
                  · linarith only [h0, h129, h131, h132, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi3]
                · linarith only [h128, h131, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h167 | h167
                    · linarith only [h1, h128, h130, h167, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h169 | h169
                      · linarith only [h128, h167, h169, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                      · rcases h5bigk with h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h0, h128, h130, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p171_1, u1elo0, u3ehi3]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h0, h128, h130, h5, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p171_1, u1elo0, u3ehi3]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h0, h169, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p171_1, u1elo0, u3ehi3]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h0, h128, h130, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p171_1, u1elo0, u3ehi3]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h0, hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h5, hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h169, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p171_1, u1elo4, u3ehi3]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h130, hlam, p171_1]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h2, hlam, p171_1]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p171_1]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h0, h169, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p171_1, u1elo0, u3ehi3]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h167, hlam, p171_1]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h3, hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h129, hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h166, hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h169, hlam, p171_1]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h4, hlam, p171_0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h129, h169, hc45, hlam, hphi, ht34, p171_1, u3ehi3]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h0, h4, hc25, hlam, hphi, ht01, ht0b, ht5b, p171_1, u1elo0]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [h0, h169, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p171_1, u1elo0, u3ehi3]
                        · have p171_0 := h171c.1
                          have p171_1 := h171c.2.1
                          have p171_2 := h171c.2.2.1
                          have p171_3 := h171c.2.2.2
                          linarith only [hlam, p171_0]
                  · linarith only [h0, h129, h166, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                · linarith only [h128, h165, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
            · linarith only [h128, h129, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h200 | h200
            · linarith only [h128, h200, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
              · rcases m.htr 2 3 4 (by decide) (by decide) with h203 | h203
                · rcases m.htr 2 3 5 (by decide) (by decide) with h204 | h204
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h205 | h205
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h206 | h206
                      · rcases h5bigk with h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c | h207c
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p207_1, u1elo0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h0, h200, h204, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p207_1, u1elo0, u3ehi1]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h0, h200, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p207_1, u1elo0, u3ehi1]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p207_1, u1elo0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h0, hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h5, hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h200, hlam, p207_1]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p207_1, u1elo4]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h2, hlam, p207_1]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p207_1]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h0, h2, h200, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p207_1, u1elo0, u3ehi1]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h0, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p207_1, u1elo0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h3, hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h200, hc35, hlam, hphi, p207_1, u3ehi1]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h204, hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h0, h2, h204, hc45, hlam, hphi, ht01, ht0b, ht5b, p207_1, u1elo0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h4, hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h202, hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h205, hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [h206, hlam, p207_0]
                        · have p207_0 := h207c.1
                          have p207_1 := h207c.2.1
                          have p207_2 := h207c.2.2.1
                          have p207_3 := h207c.2.2.2
                          linarith only [hlam, p207_0]
                      · linarith only [h0, h128, h206, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                    · linarith only [h128, h202, h203, h205, hlam]
                  · linarith only [h128, h203, h204, hc35, hlam, hphi, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h203, h236, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h238 | h238
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h239 | h239
                      · rcases h5bigk with h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h0, h200, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p240_1, u1elo0, u3ehi1]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h0, hc25, hlam, hphi, ht01, ht0b, ht5b, p240_1, u1elo0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h0, h200, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p240_1, u1elo0, u3ehi1]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p240_1, u1elo0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h0, hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h5, hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h200, hlam, p240_1]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p240_1, u1elo4]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h2, hlam, p240_1]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p240_1]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h236, hlam, p240_1]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p240_1]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h3, hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h0, h200, h3, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p240_1, u1elo0, u3ehi1]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h0, h3, hc25, hlam, hphi, ht01, ht0b, ht5b, p240_1, u1elo0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h0, h3, hc45, hlam, hphi, ht01, ht0b, ht5b, p240_1, u1elo0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h4, hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h202, hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h238, hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [h239, hlam, p240_0]
                        · have p240_0 := h240c.1
                          have p240_1 := h240c.2.1
                          have p240_2 := h240c.2.2.1
                          have p240_3 := h240c.2.2.2
                          linarith only [hlam, p240_0]
                      · linarith only [h128, h239, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h202, h203, h238, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h268 | h268
                · rcases m.htr 2 3 5 (by decide) (by decide) with h269 | h269
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h270 | h270
                    · linarith only [h1, h128, h202, h270, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h128, h268, h270, hc45, hlam, hphi, ht34, u3ehi1]
                  · linarith only [h128, h268, h269, hc35, hlam, hphi, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h274 | h274
                  · linarith only [h268, h274, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h276 | h276
                    · linarith only [h1, h128, h202, h276, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h278 | h278
                      · linarith only [h128, h202, h278, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h128, h278, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h281 | h281
        · rcases m.htr 1 3 4 (by decide) (by decide) with h282 | h282
          · rcases m.htr 1 3 5 (by decide) (by decide) with h283 | h283
            · rcases m.htr 1 4 5 (by decide) (by decide) with h284 | h284
              · linarith only [h0, h284, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h286 | h286
                · rcases m.htr 2 3 5 (by decide) (by decide) with h287 | h287
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h288 | h288
                    · linarith only [h1, h288, h4, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h290 | h290
                      · linarith only [h1, h286, h290, h4, hlam]
                      · rcases h5bigk with h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c | h292c
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [hlam, p292_0]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h281, h286, h288, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p292_1, u3ehi3]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h0, h286, h288, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p292_1, u1elo0, u3ehi3]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h0, hc35, hlam, hphi, ht01, ht0b, ht5b, p292_1, u1elo0]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h4, hlam, p292_1]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h0, hlam, p292_0]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [hlam, p292_0]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h286, h288, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p292_1, u1elo4, u3ehi3]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p292_1, u1elo0, u3ehi4]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h284, hlam, p292_1]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h2, hlam, p292_1]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h281, hlam, p292_1]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [hlam, p292_0]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p292_1, u3ehi4]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h288, hlam, p292_1]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h3, hlam, p292_0]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h283, hlam, p292_0]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h287, hlam, p292_0]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [hlam, p292_0]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h290, hlam, p292_1]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h3, hc45, hlam, hphi, ht34, p292_1, u3ehi4]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h283, hc45, hlam, hphi, ht34, p292_1, u3ehi4]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [h287, hc45, hlam, hphi, ht34, p292_1, u3ehi4]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [hc45, hlam, hphi, ht34, p292_1, u3ehi4]
                        · have p292_0 := h292c.1
                          have p292_1 := h292c.2.1
                          have p292_2 := h292c.2.2.1
                          have p292_3 := h292c.2.2.2
                          linarith only [hlam, p292_0]
                  · linarith only [h286, h287, hc35, hlam, hphi, u3ehi3]
                · linarith only [h282, h286, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
            · linarith only [h282, h283, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h321 | h321
            · linarith only [h282, h321, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h323 | h323
              · linarith only [h3, h321, h323, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h325 | h325
                · linarith only [h1, h282, h325, h4, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h327 | h327
                  · linarith only [h321, h325, h327, hc34, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h329 | h329
                    · linarith only [h1, h329, h4, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h331 | h331
                      · linarith only [h3, h321, h331, h4, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h282, h331, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h334 | h334
          · rcases m.htr 1 3 5 (by decide) (by decide) with h335 | h335
            · rcases m.htr 1 4 5 (by decide) (by decide) with h336 | h336
              · linarith only [h2, h281, h336, h4, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h338 | h338
                · rcases m.htr 2 3 5 (by decide) (by decide) with h339 | h339
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h340 | h340
                    · linarith only [h1, h340, h4, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h342 | h342
                      · linarith only [h1, h338, h342, h4, hlam]
                      · rcases h5bigk with h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c | h344c
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [hlam, p344_0]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h335, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p344_1, u3ehi4]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h281, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p344_1]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h0, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p344_1, u1elo0, u3ehi4]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h4, hlam, p344_1]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h0, hlam, p344_0]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [hlam, p344_0]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h281, hlam, p344_0]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p344_1, u1elo4, u3ehi4]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h336, hlam, p344_1]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h2, hlam, p344_1]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p344_1]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [hlam, p344_0]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p344_1, u1elo0, u3ehi4]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h340, hlam, p344_1]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h3, hlam, p344_0]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h335, hlam, p344_0]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h339, hlam, p344_0]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [hlam, p344_0]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h342, hlam, p344_1]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h0, h334, h336, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h334, h336, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [h281, h334, h336, hc45, hlam, hphi, ht34, p344_1, u3ehi3]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [hc45, hlam, hphi, ht34, p344_1, u3ehi4]
                        · have p344_0 := h344c.1
                          have p344_1 := h344c.2.1
                          have p344_2 := h344c.2.2.1
                          have p344_3 := h344c.2.2.2
                          linarith only [hlam, p344_0]
                  · linarith only [h338, h339, hc35, hlam, hphi, u3ehi3]
                · linarith only [h0, h334, h336, h338, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
            · linarith only [h334, h335, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h373 | h373
            · linarith only [h334, h373, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
              · linarith only [h3, h373, h375, h4, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
                · linarith only [h1, h334, h377, h4, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h379 | h379
                  · linarith only [h373, h377, h379, hc34, hlam, hphi, u3ehi1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h381 | h381
                    · linarith only [h1, h381, h4, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h383 | h383
                      · linarith only [h3, h373, h383, h4, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h334, h383, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h386 | h386
      · rcases m.htr 1 2 5 (by decide) (by decide) with h387 | h387
        · rcases m.htr 1 3 4 (by decide) (by decide) with h388 | h388
          · rcases m.htr 1 3 5 (by decide) (by decide) with h389 | h389
            · linarith only [h3, h389, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · linarith only [h388, h389, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h392 | h392
            · linarith only [h388, h392, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h394 | h394
              · rcases m.htr 2 3 4 (by decide) (by decide) with h395 | h395
                · rcases m.htr 2 3 5 (by decide) (by decide) with h396 | h396
                  · linarith only [h0, h387, h392, h396, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                  · linarith only [h388, h395, h396, hc35, hlam, hphi, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h399 | h399
                  · linarith only [h3, h395, h399, hc34, hlam, hphi, u3ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h401 | h401
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h402 | h402
                      · rcases h5bigk with h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c | h403c
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p403_1, u1elo0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h0, h399, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p403_1, u1elo0, u3ehi2]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h3, hlam, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p403_1, u1elo0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h0, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h399, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p403_1, u1elo4, u3ehi2]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h392, hlam, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p403_1, u1elo0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h2, hlam, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h387, hlam, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h399, hlam, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p403_1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h3, hc35, hlam, hphi, p403_1, u3ehi0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h392, hc35, hlam, hphi, p403_1, u3ehi1]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h399, hc35, hlam, hphi, p403_1, u3ehi2]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          rcases p403_3 (m.d 0 5) (by simp) with h423 | h423
                          · linarith only [h3, h423, hlam]
                          · linarith only [h386, h423, hlam]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h386, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h394, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h401, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [h402, hlam, p403_0]
                        · have p403_0 := h403c.1
                          have p403_1 := h403c.2.1
                          have p403_2 := h403c.2.2.1
                          have p403_3 := h403c.2.2.2
                          linarith only [hlam, p403_0]
                      · linarith only [h386, h388, h402, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h394, h395, h401, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h433 | h433
                · rcases m.htr 2 3 5 (by decide) (by decide) with h434 | h434
                  · linarith only [h0, h3, h387, h434, hlam]
                  · linarith only [h433, h434, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h437 | h437
                  · linarith only [h1, h3, h433, h437, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h439 | h439
                    · linarith only [h388, h394, h433, h439, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h441 | h441
                      · linarith only [h388, h394, h441, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h3, h386, h388, h441, hc35, hlam, hphi, u3ehi1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h444 | h444
          · rcases m.htr 1 3 5 (by decide) (by decide) with h445 | h445
            · linarith only [h3, h445, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · linarith only [h444, h445, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h448 | h448
            · linarith only [h444, h448, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h450 | h450
              · rcases m.htr 2 3 4 (by decide) (by decide) with h451 | h451
                · rcases m.htr 2 3 5 (by decide) (by decide) with h452 | h452
                  · linarith only [h2, h3, h452, hlam]
                  · linarith only [h451, h452, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h455 | h455
                  · linarith only [h1, h3, h451, h455, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h457 | h457
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h458 | h458
                      · rcases h5bigk with h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c | h459c
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht5b, p459_1, u1elo0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h0, h387, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p459_1, u1elo0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h3, hlam, p459_1]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h0, hc45, hlam, hphi, ht01, ht0b, ht5b, p459_1, u1elo0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h0, hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h387, hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h448, hlam, p459_1]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht5b, p459_1, u1elo4]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h2, hlam, p459_1]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h2, hc02, hc15, hlam, hphi, ht0b, ht5b, p459_1]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h455, hlam, p459_1]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h0, h2, hc45, hlam, hphi, ht01, ht0b, ht5b, p459_1, u1elo0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h0, h448, h458, hc34, hlam, hphi, p459_1, u3ehi1]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h448, h458, hc34, hlam, hphi, p459_1, u3ehi1]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h387, h448, h458, hc34, hlam, hphi, p459_1, u3ehi1]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          rcases p459_3 (m.d 0 5) (by simp) with h479 | h479
                          · linarith only [h3, h479, hlam]
                          · linarith only [h386, h479, hlam]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h386, hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h450, hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h457, hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [h458, hlam, p459_0]
                        · have p459_0 := h459c.1
                          have p459_1 := h459c.2.1
                          have p459_2 := h459c.2.2.1
                          have p459_3 := h459c.2.2.2
                          linarith only [hlam, p459_0]
                      · linarith only [h0, h386, h444, h458, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi1]
                    · linarith only [h450, h451, h457, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h489 | h489
                · rcases m.htr 2 3 5 (by decide) (by decide) with h490 | h490
                  · linarith only [h2, h3, h490, hlam]
                  · linarith only [h489, h490, hc35, hlam, hphi, u3ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h493 | h493
                  · linarith only [h1, h3, h489, h493, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h495 | h495
                    · linarith only [h444, h450, h489, h495, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h497 | h497
                      · linarith only [h444, h450, h497, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h3, h386, h444, h497, hc35, hlam, hphi, u3ehi1]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
        · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
          · rcases m.htr 1 3 5 (by decide) (by decide) with h502 | h502
            · linarith only [h3, h502, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · linarith only [h501, h502, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h505 | h505
            · linarith only [h501, h505, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h507 | h507
              · linarith only [h0, h386, h507, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h509 | h509
                · linarith only [h1, h386, h501, h509, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h511 | h511
                  · linarith only [h509, h511, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h513 | h513
                    · linarith only [h1, h386, h513, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h515 | h515
                      · linarith only [h501, h507, h515, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h501, h515, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h518 | h518
          · rcases m.htr 1 3 5 (by decide) (by decide) with h519 | h519
            · linarith only [h3, h519, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · linarith only [h518, h519, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h522 | h522
            · linarith only [h518, h522, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h524 | h524
              · linarith only [h2, h386, h500, h524, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h526 | h526
                · linarith only [h1, h386, h518, h526, hc45, hlam, hphi, ht34, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h528 | h528
                  · linarith only [h526, h528, hc34, hlam, hphi, u3ehi4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h530 | h530
                    · linarith only [h1, h386, h530, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h532 | h532
                      · linarith only [h518, h524, h532, hc34, hlam, hphi, u3ehi1]
                      · linarith only [h518, h532, hc45, hlam, hphi, ht34, u3ehi1]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h535 | h535
    · rcases m.htr 0 4 5 (by decide) (by decide) with h536 | h536
      · linarith only [h1, h2, h536, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h538 | h538
        · linarith only [h1, h2, h538, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h540 | h540
          · rcases m.htr 1 3 5 (by decide) (by decide) with h541 | h541
            · rcases m.htr 1 4 5 (by decide) (by decide) with h542 | h542
              · linarith only [h0, h536, h542, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h544 | h544
                · rcases m.htr 2 3 5 (by decide) (by decide) with h545 | h545
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h546 | h546
                    · linarith only [h1, h2, h536, h546, hlam]
                    · linarith only [h1, h2, h544, h546, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h0, h541, h545, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0, u3ehi2]
                · linarith only [h540, h544, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi2]
            · linarith only [h540, h541, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h552 | h552
            · linarith only [h540, h552, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h554 | h554
              · linarith only [h535, h536, h552, h554, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3, u3ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h556 | h556
                · linarith only [h1, h2, h540, h556, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h558 | h558
                  · linarith only [h552, h556, h558, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h2, h535, h558, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
      · linarith only [h1, h2, h561, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h563 | h563
        · linarith only [h1, h2, h563, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h565 | h565
          · rcases m.htr 1 3 5 (by decide) (by decide) with h566 | h566
            · linarith only [h535, h566, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo2, u3ehi0]
            · linarith only [h565, h566, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h569 | h569
            · linarith only [h565, h569, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h571 | h571
              · linarith only [h0, h561, h571, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h573 | h573
                · linarith only [h1, h2, h565, h573, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h575 | h575
                  · linarith only [h573, h575, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1, h2, h573, h575, hc35, hlam, hphi, u3ehi2]

end R2N4
