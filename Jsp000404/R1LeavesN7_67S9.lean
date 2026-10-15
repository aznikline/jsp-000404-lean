import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_14_M_LR_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 4 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h6, h9, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h7, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h0, h11, h7, h8, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                  · linarith only [h0, h14, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h16, h7, h8, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h14, h18, h2, h4, h7, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h14, h18, h2, h4, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h3, h6, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h22 | h22
              · linarith only [h0, h2, h22, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h24 | h24
                · rcases m.htr 2 3 4 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
                      · linarith only [h0, h2, h25, h27, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h1, h24, h27, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h22, h24, h26, hlam]
                  · linarith only [h0, h2, h25, h4, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h32 | h32
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h33 | h33
                    · linarith only [h0, h2, h24, h32, h33, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h2, h22, h33, h4, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h2, h32, h4, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
            · rcases m.htr 1 2 4 (by decide) (by decide) with h38 | h38
              · rcases m.htr 1 4 5 (by decide) (by decide) with h39 | h39
                · linarith only [h39, h5, hc14, hlam, hphi, ht01, u0ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                  · linarith only [h0, h37, h41, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h43 | h43
                    · linarith only [h0, h38, h43, h5, hlam, hphi, u0ehi8, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                      · linarith only [h0, h2, h4, h45, h5, hlam, hphi, u0ehi8, u0elo0]
                      · rcases h4bigk with h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h5, hc14, hc45, hlam, hphi, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h5, hc24, hc45, hlam, hphi, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h41, h5, hc23, hc45, hlam, hphi, ht34, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h5, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h1, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h1, hc24, hlam, hphi, ht0b, ht45, ht5b, p47_1, u0elo0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h0, h38, h41, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p47_1, u0elo0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h39, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h3, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h38, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h41, hlam, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h43, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h4, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h0, h2, h4, hc14, hlam, hphi, ht0b, ht45, ht5b, p47_1, u0elo0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h0, h2, h4, h41, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p47_1, u0elo0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h45, hlam, p47_0]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p47_1, u0ehi8]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          rcases p47_3 (m.d 0 4) (by simp) with h69 | h69
                          · linarith only [h5, h69, hlam]
                          · linarith only [h1, h69, hlam]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          rcases p47_3 (m.d 0 4) (by simp) with h72 | h72
                          · linarith only [h5, h72, hlam]
                          · linarith only [h3, h72, hlam]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [h41, hc23, hc45, hlam, hphi, ht34, p47_1]
                        · have p47_0 := h47c.1
                          have p47_1 := h47c.2.1
                          have p47_2 := h47c.2.2.1
                          have p47_3 := h47c.2.2.2
                          linarith only [hlam, p47_0]
              · linarith only [h0, h3, h37, h38, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h78 | h78
              · linarith only [h0, h2, h37, h78, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                · linarith only [h5, h80, hc14, hlam, hphi, ht01, u0ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h83 | h83
                    · linarith only [h0, h2, h5, h82, h83, hlam, hphi, u0ehi8, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h85 | h85
                      · linarith only [h0, h2, h5, h82, h85, hlam, hphi, u0ehi8, u0elo0]
                      · rcases h4bigk with h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c | h87c
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h5, hc14, hc45, hlam, hphi, p87_1]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h5, h78, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h5, hc34, hc45, hlam, hphi, p87_1]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h5, hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h1, hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h78, hlam, p87_1]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1, u0elo0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h80, hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h3, hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h0, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p87_1, u0elo0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h0, h2, h82, hc34, hlam, hphi, ht0b, ht45, ht5b, p87_1, u0elo0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h83, hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h4, hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h0, h2, h4, h78, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p87_1, u0elo0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h82, hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h85, hlam, p87_0]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p87_1, u0ehi8]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          rcases p87_3 (m.d 0 4) (by simp) with h109 | h109
                          · linarith only [h109, h5, hlam]
                          · linarith only [h1, h109, hlam]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [h78, hc12, hc45, hlam, hphi, ht23, ht34, p87_1]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          rcases p87_3 (m.d 0 4) (by simp) with h113 | h113
                          · linarith only [h113, h5, hlam]
                          · linarith only [h113, h4, hlam]
                        · have p87_0 := h87c.1
                          have p87_1 := h87c.2.1
                          have p87_2 := h87c.2.2.1
                          have p87_3 := h87c.2.2.2
                          linarith only [hlam, p87_0]
                  · linarith only [h0, h2, h37, h4, h82, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h118 | h118
          · rcases m.htr 1 2 3 (by decide) (by decide) with h119 | h119
            · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
              · rcases m.htr 1 4 5 (by decide) (by decide) with h121 | h121
                · rcases m.htr 2 3 4 (by decide) (by decide) with h122 | h122
                  · linarith only [h0, h119, h122, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h124 | h124
                    · linarith only [h0, h120, h124, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h1, h121, h122, h124, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h127 | h127
                  · linarith only [h119, h127, h4, hc13, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h129 | h129
                    · linarith only [h120, h121, h129, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h131 | h131
                      · rcases h4bigk with h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c | h132c
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          rcases p132_3 (m.d 0 4) (by simp) with h134 | h134
                          · rcases p132_3 (m.d 1 4) (by simp) with h135 | h135
                            · linarith only [h1, h135, hlam]
                            · rcases p132_3 (m.d 2 4) (by simp) with h137 | h137
                              · linarith only [h137, h3, hlam]
                              · rcases p132_3 (m.d 3 4) (by simp) with h139 | h139
                                · rcases p132_3 (m.d 4 5) (by simp) with h140 | h140
                                  · linarith only [h118, h140, hlam]
                                  · linarith only [h121, h140, hlam]
                                · linarith only [h118, h121, h139, h4, hlam, hphi, u0ehi7, u0elo3]
                          · linarith only [h1, h134, hlam]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          rcases p132_3 (m.d 0 4) (by simp) with h145 | h145
                          · rcases p132_3 (m.d 1 4) (by simp) with h146 | h146
                            · linarith only [h1, h146, hlam]
                            · linarith only [h120, h146, hlam]
                          · linarith only [h145, h3, hlam]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h4, hlam, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h121, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p132_1, u0elo0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h1, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h121, h127, hc23, hc45, hlam, hphi, ht34, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h118, h121, h3, h4, hlam, hphi, p132_1, u0ehi7, u0elo0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h121, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h3, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h120, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h127, hlam, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h129, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h118, h121, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          rcases p132_3 (m.d 0 4) (by simp) with h163 | h163
                          · linarith only [h163, h4, hlam]
                          · linarith only [h1, h163, hlam]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          rcases p132_3 (m.d 0 4) (by simp) with h166 | h166
                          · linarith only [h166, h4, hlam]
                          · linarith only [h166, h3, hlam]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h120, h121, h127, hc23, hc34, hlam, hphi, p132_1]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h118, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h118, h120, h127, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p132_1, u0elo0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h0, h118, h127, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p132_1, u0elo0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [h131, hlam, p132_0]
                        · have p132_0 := h132c.1
                          have p132_1 := h132c.2.1
                          have p132_2 := h132c.2.2.1
                          have p132_3 := h132c.2.2.2
                          linarith only [hlam, p132_0]
                      · linarith only [h0, h118, h131, h3, h4, hlam, hphi, u0ehi7, u0elo0]
              · linarith only [h0, h119, h120, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h178 | h178
              · linarith only [h0, h119, h178, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
                · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                  · linarith only [h0, h181, h2, h4, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h183 | h183
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h184 | h184
                      · rcases h4bigk with h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c | h185c
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h0, h180, h3, hc45, hlam, hphi, ht0b, ht5b, p185_1, u0elo0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h0, h119, h181, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p185_1, u0elo0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h4, hlam, p185_1]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          rcases p185_3 (m.d 0 4) (by simp) with h190 | h190
                          · rcases p185_3 (m.d 1 4) (by simp) with h191 | h191
                            · linarith only [h1, h191, hlam]
                            · linarith only [h180, h191, hlam]
                          · linarith only [h190, hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h1, hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h178, hlam, p185_1]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h4, hc14, hlam, hphi, ht01, p185_1, u0ehi7]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p185_1, u0elo0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h3, hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h0, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p185_1, u0elo0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h181, hlam, p185_1]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h0, h3, hc45, hlam, hphi, ht0b, ht5b, p185_1, u0elo0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h0, h119, h181, h3, hc12, hc34, hlam, hphi, ht23, p185_1, u0ehi8, u0elo0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          rcases p185_3 (m.d 0 4) (by simp) with h206 | h206
                          · linarith only [h206, h4, hlam]
                          · linarith only [h1, h206, hlam]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h119, h181, hc12, hc34, hlam, hphi, ht23, p185_1]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          rcases p185_3 (m.d 0 4) (by simp) with h211 | h211
                          · linarith only [h211, h4, hlam]
                          · linarith only [h118, h211, hlam]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h118, hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h180, hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h183, hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [h184, hlam, p185_0]
                        · have p185_0 := h185c.1
                          have p185_1 := h185c.2.1
                          have p185_2 := h185c.2.2.1
                          have p185_3 := h185c.2.2.2
                          linarith only [hlam, p185_0]
                      · linarith only [h1, h180, h184, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h178, h180, h183, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h221 | h221
                  · linarith only [h0, h118, h178, h180, h221, h3, h4, hc12, hc23, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h223 | h223
                    · linarith only [h0, h178, h180, h223, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h118, h119, h221, h223, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h226 | h226
            · rcases m.htr 1 2 4 (by decide) (by decide) with h227 | h227
              · rcases m.htr 1 4 5 (by decide) (by decide) with h228 | h228
                · linarith only [h118, h228, hc14, hlam, hphi, ht01, u0ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h230 | h230
                  · linarith only [h226, h230, h4, hc12, hlam, hphi, ht01, u0ehi7]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h232 | h232
                    · linarith only [h0, h118, h227, h232, h4, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h234 | h234
                      · linarith only [h118, h234, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                      · linarith only [h234, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h0, h226, h227, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h238 | h238
              · linarith only [h0, h2, h226, h238, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h240 | h240
                · linarith only [h118, h240, h4, hc14, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
                  · linarith only [h0, h2, h242, h4, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h244 | h244
                    · linarith only [h0, h118, h244, h3, h4, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h246 | h246
                      · linarith only [h0, h118, h226, h242, h246, h3, h4, hc12, hc34, hlam, hphi, ht23, u0ehi7, u0elo0]
                      · linarith only [h0, h226, h242, h246, h3, h4, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h249 | h249
        · linarith only [h2, h249, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h251 | h251
          · rcases m.htr 1 2 3 (by decide) (by decide) with h252 | h252
            · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
              · linarith only [h0, h253, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
                · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                  · linarith only [h1, h252, h253, h256, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h259 | h259
                      · rcases h4bigk with h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c | h260c
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h252, h253, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p260_1, u0elo3]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h3, hlam, p260_1]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h249, hlam, p260_1]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          rcases p260_3 (m.d 0 4) (by simp) with h265 | h265
                          · rcases p260_3 (m.d 1 4) (by simp) with h266 | h266
                            · linarith only [h1, h266, hlam]
                            · linarith only [h255, h266, hlam]
                          · linarith only [h265, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h1, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h253, hlam, p260_1]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h2, h256, h3, hc14, hlam, hphi, ht01, p260_1, u0ehi7]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p260_1, u0elo0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hc24, hlam, hphi, ht01, ht12, p260_1, u0ehi8]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h252, h253, h256, hc23, hc34, hlam, hphi, p260_1]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h256, hlam, p260_1]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          rcases p260_3 (m.d 0 4) (by simp) with h279 | h279
                          · linarith only [h279, h3, hlam]
                          · linarith only [h251, h279, hlam]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h2, h3, hc34, hlam, hphi, ht01, ht12, ht23, p260_1, u0ehi7]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h252, h253, hc23, hc34, hlam, hphi, p260_1]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h2, h3, hc34, hlam, hphi, ht01, ht12, ht23, p260_1, u0ehi7]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          rcases p260_3 (m.d 0 4) (by simp) with h286 | h286
                          · linarith only [h249, h286, hlam]
                          · linarith only [h251, h286, hlam]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h251, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h255, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h258, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [h259, hlam, p260_0]
                        · have p260_0 := h260c.1
                          have p260_1 := h260c.2.1
                          have p260_2 := h260c.2.2.1
                          have p260_3 := h260c.2.2.2
                          linarith only [hlam, p260_0]
                      · linarith only [h2, h256, h259, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                    · linarith only [h2, h255, h258, h3, hc14, hlam, hphi, ht01, u0ehi7]
                · linarith only [h251, h252, h253, h255, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
            · linarith only [h2, h252, h3, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
            · rcases m.htr 1 2 4 (by decide) (by decide) with h299 | h299
              · linarith only [h0, h2, h299, h3, hlam, hphi, u0ehi7, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h301 | h301
                · linarith only [h1, h2, h251, h3, h301, hlam, hphi, u0ehi7, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h303 | h303
                  · linarith only [h1, h2, h251, h298, h299, h3, h303, hc34, hc45, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h305 | h305
                    · linarith only [h2, h251, h3, h305, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h2, h3, h305, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
            · linarith only [h2, h298, h3, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
      · rcases m.htr 0 3 4 (by decide) (by decide) with h310 | h310
        · rcases m.htr 0 4 5 (by decide) (by decide) with h311 | h311
          · rcases m.htr 1 2 3 (by decide) (by decide) with h312 | h312
            · linarith only [h2, h312, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h314 | h314
              · rcases m.htr 1 4 5 (by decide) (by decide) with h315 | h315
                · rcases m.htr 2 3 4 (by decide) (by decide) with h316 | h316
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h317 | h317
                    · linarith only [h0, h314, h317, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h0, h314, h315, h316, h317, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h2, h309, h311, h316, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h322 | h322
                    · linarith only [h314, h315, h322, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h324 | h324
                      · linarith only [h314, h315, h321, h324, hlam]
                      · rcases h4bigk with h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c | h326c
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          rcases p326_3 (m.d 0 4) (by simp) with h328 | h328
                          · rcases p326_3 (m.d 1 4) (by simp) with h329 | h329
                            · linarith only [h1, h329, hlam]
                            · rcases p326_3 (m.d 2 4) (by simp) with h331 | h331
                              · linarith only [h309, h331, hlam]
                              · rcases p326_3 (m.d 3 4) (by simp) with h333 | h333
                                · linarith only [h310, h333, hlam]
                                · rcases p326_3 (m.d 4 5) (by simp) with h335 | h335
                                  · linarith only [h311, h335, hlam]
                                  · linarith only [h315, h335, hlam]
                          · linarith only [h1, h328, hlam]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          rcases p326_3 (m.d 0 4) (by simp) with h339 | h339
                          · rcases p326_3 (m.d 1 4) (by simp) with h340 | h340
                            · linarith only [h1, h340, hlam]
                            · linarith only [h314, h340, hlam]
                          · linarith only [h309, h339, hlam]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          rcases p326_3 (m.d 0 4) (by simp) with h344 | h344
                          · rcases p326_3 (m.d 1 4) (by simp) with h345 | h345
                            · linarith only [h1, h345, hlam]
                            · linarith only [h314, h321, h345, hlam]
                          · linarith only [h310, h344, hlam]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h309, h314, h315, h321, hc34, hlam, hphi, ht0b, ht45, ht5b, p326_1, u0elo1]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h1, hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h315, h321, hc34, hc45, hlam, hphi, p326_1]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h2, h309, h311, h315, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p326_1]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h315, hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h309, hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h314, hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h2, h309, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p326_1]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h322, hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h310, hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h310, hc14, hlam, hphi, ht0b, ht45, ht5b, p326_1, u0elo2]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h321, hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h324, hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h311, hlam, p326_0]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h2, h309, h311, h314, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p326_1]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h2, h309, h311, h321, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p326_1]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [h2, h309, h311, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p326_1]
                        · have p326_0 := h326c.1
                          have p326_1 := h326c.2.1
                          have p326_2 := h326c.2.2.1
                          have p326_3 := h326c.2.2.2
                          linarith only [hlam, p326_0]
                  · linarith only [h2, h321, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · linarith only [h2, h309, h314, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h372 | h372
            · linarith only [h2, h372, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h374 | h374
              · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                · linarith only [h311, h375, hc14, hlam, hphi, ht01, u0ehi8]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                    · linarith only [h0, h374, h378, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h380 | h380
                      · linarith only [h0, h311, h374, h377, h380, hlam, hphi, u0ehi8, u0elo0]
                      · rcases h4bigk with h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c | h382c
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h311, hc14, hc45, hlam, hphi, p382_1]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h311, hc24, hc45, hlam, hphi, p382_1]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h311, hc34, hc45, hlam, hphi, p382_1]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h311, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h1, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h1, h377, hc34, hlam, hphi, ht0b, ht45, ht5b, p382_1, u0elo0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h0, h374, hc34, hlam, hphi, ht0b, ht45, ht5b, p382_1, u0elo0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h375, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h309, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h374, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h309, hc34, hlam, hphi, ht0b, ht45, ht5b, p382_1, u0elo1]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h378, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h310, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h310, hc14, hlam, hphi, ht0b, ht45, ht5b, p382_1, u0elo2]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h377, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [h380, hlam, p382_0]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p382_1, u0ehi8]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          rcases p382_3 (m.d 0 4) (by simp) with h404 | h404
                          · linarith only [h311, h404, hlam]
                          · linarith only [h1, h404, hlam]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          rcases p382_3 (m.d 0 4) (by simp) with h407 | h407
                          · linarith only [h311, h407, hlam]
                          · linarith only [h309, h407, hlam]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          rcases p382_3 (m.d 0 4) (by simp) with h410 | h410
                          · linarith only [h311, h410, hlam]
                          · linarith only [h310, h410, hlam]
                        · have p382_0 := h382c.1
                          have p382_1 := h382c.2.1
                          have p382_2 := h382c.2.2.1
                          have p382_3 := h382c.2.2.2
                          linarith only [hlam, p382_0]
                  · linarith only [h2, h377, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · linarith only [h2, h309, h374, hc12, hc23, hlam, hphi]
        · linarith only [h2, h309, h310, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h417 | h417
        · rcases m.htr 0 4 5 (by decide) (by decide) with h418 | h418
          · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
            · linarith only [h2, h419, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h421 | h421
              · linarith only [h0, h309, h421, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h423 | h423
                · rcases m.htr 2 3 4 (by decide) (by decide) with h424 | h424
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h425 | h425
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h426 | h426
                      · rcases h4bigk with h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c | h427c
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h417, h423, hc45, hlam, hphi, ht0b, ht5b, p427_1, u0elo2]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h309, hlam, p427_1]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h417, h426, hc45, hlam, hphi, ht0b, ht5b, p427_1, u0elo2]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          rcases p427_3 (m.d 0 4) (by simp) with h432 | h432
                          · rcases p427_3 (m.d 1 4) (by simp) with h433 | h433
                            · linarith only [h1, h433, hlam]
                            · linarith only [h423, h433, hlam]
                          · linarith only [h432, hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h1, hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h421, hlam, p427_1]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h1, h426, hc45, hlam, hphi, ht0b, ht5b, p427_1, u0elo0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p427_1, u0elo0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h424, hc23, hlam, hphi, ht01, ht12, p427_1, u0ehi8]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          rcases p427_3 (m.d 0 4) (by simp) with h443 | h443
                          · linarith only [h309, h443, hlam]
                          · linarith only [h1, h443, hlam]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          rcases p427_3 (m.d 0 4) (by simp) with h447 | h447
                          · linarith only [h309, h447, hlam]
                          · linarith only [h417, h447, hlam]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          rcases p427_3 (m.d 0 4) (by simp) with h450 | h450
                          · linarith only [h309, h450, hlam]
                          · linarith only [h418, h450, hlam]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h417, hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h417, h423, hc45, hlam, hphi, ht0b, ht5b, p427_1, u0elo2]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h424, hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h417, hc45, hlam, hphi, ht0b, ht5b, p427_1, u0elo2]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h418, hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h423, hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h425, hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [h426, hlam, p427_0]
                        · have p427_0 := h427c.1
                          have p427_1 := h427c.2.1
                          have p427_2 := h427c.2.2.1
                          have p427_3 := h427c.2.2.2
                          linarith only [hlam, p427_0]
                      · linarith only [h1, h423, h426, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h1, h423, h425, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h2, h424, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h466 | h466
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h467 | h467
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h468 | h468
                      · linarith only [h417, h421, h423, h468, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases h4bigk with h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c | h470c
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          rcases p470_3 (m.d 0 4) (by simp) with h472 | h472
                          · rcases p470_3 (m.d 1 4) (by simp) with h473 | h473
                            · linarith only [h1, h473, hlam]
                            · rcases p470_3 (m.d 2 4) (by simp) with h475 | h475
                              · rcases p470_3 (m.d 3 4) (by simp) with h476 | h476
                                · linarith only [h417, h476, hlam]
                                · rcases p470_3 (m.d 4 5) (by simp) with h478 | h478
                                  · linarith only [h418, h478, hlam]
                                  · linarith only [h423, h478, hlam]
                              · linarith only [h421, h475, hlam]
                          · linarith only [h1, h472, hlam]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h309, hlam, p470_1]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          rcases p470_3 (m.d 0 4) (by simp) with h484 | h484
                          · rcases p470_3 (m.d 1 4) (by simp) with h485 | h485
                            · linarith only [h1, h485, hlam]
                            · rcases p470_3 (m.d 2 4) (by simp) with h487 | h487
                              · rcases p470_3 (m.d 3 4) (by simp) with h488 | h488
                                · linarith only [h417, h488, hlam]
                                · rcases p470_3 (m.d 4 5) (by simp) with h490 | h490
                                  · linarith only [h418, h490, hlam]
                                  · linarith only [h468, h490, hlam]
                              · linarith only [h466, h487, hlam]
                          · linarith only [h417, h484, hlam]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h1, h421, h423, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p470_1, u0elo0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h1, hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h421, hlam, p470_1]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h423, hc34, hc45, hlam, hphi, p470_1]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h423, hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h466, hc23, hlam, hphi, ht01, ht12, p470_1, u0ehi8]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          rcases p470_3 (m.d 0 4) (by simp) with h502 | h502
                          · linarith only [h309, h502, hlam]
                          · linarith only [h1, h502, hlam]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          rcases p470_3 (m.d 0 4) (by simp) with h506 | h506
                          · linarith only [h309, h506, hlam]
                          · linarith only [h417, h506, hlam]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h421, h423, h466, hc12, hc23, hlam, hphi, p470_1]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h417, hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h417, h421, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p470_1, u0elo2]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h466, hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h468, hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h418, hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h1, h418, h421, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p470_1, u0elo0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h467, hlam, p470_0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [h1, h418, hc34, hlam, hphi, ht0b, ht45, ht5b, p470_1, u0elo0]
                        · have p470_0 := h470c.1
                          have p470_1 := h470c.2.1
                          have p470_2 := h470c.2.2.1
                          have p470_3 := h470c.2.2.2
                          linarith only [hlam, p470_0]
                    · linarith only [h1, h309, h418, h467, hlam, hphi, u0ehi6, u0elo0]
                  · linarith only [h2, h466, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h522 | h522
            · linarith only [h2, h522, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h524 | h524
              · linarith only [h0, h309, h524, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h526 | h526
                · linarith only [h1, h418, h526, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h528 | h528
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h529 | h529
                    · linarith only [h309, h418, h528, h529, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h309, h529, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                  · linarith only [h2, h417, h528, hlam, hphi, u0ehi6, u0elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h533 | h533
          · rcases m.htr 1 2 3 (by decide) (by decide) with h534 | h534
            · linarith only [h2, h534, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h536 | h536
              · linarith only [h0, h309, h536, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h538 | h538
                · rcases m.htr 2 3 4 (by decide) (by decide) with h539 | h539
                  · linarith only [h2, h417, h539, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · linarith only [h2, h539, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h542 | h542
                  · linarith only [h1, h2, h417, h533, h536, h538, h542, hc12, hc23, hlam, hphi, u0ehi6, u0elo0]
                  · linarith only [h1, h2, h533, h536, h538, h542, hc12, hc34, hlam, hphi, ht23, u0ehi6, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h545 | h545
            · linarith only [h2, h545, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h547 | h547
              · linarith only [h0, h309, h547, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h549 | h549
                · linarith only [h1, h533, h549, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h551 | h551
                  · linarith only [h2, h417, h551, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · linarith only [h2, h551, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h554 | h554
    · rcases m.htr 0 2 4 (by decide) (by decide) with h555 | h555
      · linarith only [h0, h1, h555, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h557 | h557
        · linarith only [h0, h1, h554, h557, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h559 | h559
          · rcases m.htr 1 2 3 (by decide) (by decide) with h560 | h560
            · rcases m.htr 1 2 4 (by decide) (by decide) with h561 | h561
              · linarith only [h555, h561, hc12, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h563 | h563
                · rcases m.htr 2 3 4 (by decide) (by decide) with h564 | h564
                  · linarith only [h0, h1, h557, h560, h561, h564, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                  · linarith only [h0, h1, h560, h561, h564, hc23, hc34, hlam, hphi]
                · linarith only [h0, h1, h559, h560, h563, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
            · linarith only [h554, h555, h560, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h569 | h569
            · linarith only [h0, h1, h559, h569, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h1, h554, h559, h569, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h572 | h572
      · linarith only [h0, h1, h572, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h574 | h574
        · rcases m.htr 0 4 5 (by decide) (by decide) with h575 | h575
          · rcases m.htr 1 2 3 (by decide) (by decide) with h576 | h576
            · linarith only [h554, h576, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h578 | h578
              · linarith only [h0, h572, h578, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h580 | h580
                · rcases m.htr 2 3 4 (by decide) (by decide) with h581 | h581
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h582 | h582
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h583 | h583
                      · rcases h4bigk with h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h1, hlam, p584_1]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h572, hlam, p584_1]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h574, h583, hc45, hlam, hphi, ht0b, ht5b, p584_1, u0elo2]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          rcases p584_3 (m.d 0 4) (by simp) with h589 | h589
                          · rcases p584_3 (m.d 1 4) (by simp) with h590 | h590
                            · rcases p584_3 (m.d 2 4) (by simp) with h591 | h591
                              · rcases p584_3 (m.d 3 4) (by simp) with h592 | h592
                                · linarith only [h574, h592, hlam]
                                · linarith only [h583, h592, hlam]
                              · linarith only [h582, h591, hlam]
                            · linarith only [h580, h590, hlam]
                          · linarith only [h589, hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h578, h581, hc23, hlam, hphi, ht01, ht12, p584_1, u0ehi8]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h578, hlam, p584_1]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          rcases p584_3 (m.d 0 4) (by simp) with h601 | h601
                          · linarith only [h1, h601, hlam]
                          · linarith only [h574, h601, hlam]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          rcases p584_3 (m.d 0 4) (by simp) with h604 | h604
                          · linarith only [h1, h604, hlam]
                          · linarith only [h575, h604, hlam]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h0, h1, h581, hc12, hc23, hlam, hphi, p584_1]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h0, h1, h581, hc23, hlam, hphi, ht01, ht12, p584_1, u0ehi6]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          rcases p584_3 (m.d 0 4) (by simp) with h610 | h610
                          · linarith only [h572, h610, hlam]
                          · linarith only [h574, h610, hlam]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          rcases p584_3 (m.d 0 4) (by simp) with h613 | h613
                          · linarith only [h572, h613, hlam]
                          · linarith only [h575, h613, hlam]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h574, hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h0, h1, hc34, hlam, hphi, ht01, ht12, ht23, p584_1, u0ehi6]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h581, hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h574, hc45, hlam, hphi, ht0b, ht5b, p584_1, u0elo2]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h575, hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h580, hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h582, hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [h583, hlam, p584_0]
                        · have p584_0 := h584c.1
                          have p584_1 := h584c.2.1
                          have p584_2 := h584c.2.2.1
                          have p584_3 := h584c.2.2.2
                          linarith only [hlam, p584_0]
                      · rcases h4bigk with h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c | h626c
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h1, hlam, p626_1]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h572, hlam, p626_1]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          rcases p626_3 (m.d 0 4) (by simp) with h630 | h630
                          · rcases p626_3 (m.d 1 4) (by simp) with h631 | h631
                            · rcases p626_3 (m.d 2 4) (by simp) with h632 | h632
                              · rcases p626_3 (m.d 3 4) (by simp) with h633 | h633
                                · linarith only [h574, h633, hlam]
                                · rcases p626_3 (m.d 4 5) (by simp) with h635 | h635
                                  · linarith only [h575, h635, hlam]
                                  · linarith only [h583, h635, hlam]
                              · linarith only [h581, h632, hlam]
                            · linarith only [h0, h1, h583, h631, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                          · linarith only [h574, h630, hlam]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h583, hc34, hlam, hphi, ht0b, ht45, ht5b, p626_1, u0elo3]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [hc14, hlam, hphi, ht01, p626_1, u0ehi8]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h578, hlam, p626_1]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          rcases p626_3 (m.d 0 4) (by simp) with h645 | h645
                          · linarith only [h1, h645, hlam]
                          · linarith only [h574, h645, hlam]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          rcases p626_3 (m.d 0 4) (by simp) with h648 | h648
                          · linarith only [h1, h648, hlam]
                          · linarith only [h575, h648, hlam]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h0, h1, h581, hc23, hlam, hphi, ht01, ht12, p626_1, u0ehi6]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h0, h1, h581, hc23, hlam, hphi, ht01, ht12, p626_1, u0ehi6]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          rcases p626_3 (m.d 0 4) (by simp) with h654 | h654
                          · linarith only [h572, h654, hlam]
                          · linarith only [h574, h654, hlam]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          rcases p626_3 (m.d 0 4) (by simp) with h657 | h657
                          · linarith only [h572, h657, hlam]
                          · linarith only [h575, h657, hlam]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h574, hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h0, h1, h575, h583, hlam, hphi, p626_1, u0ehi6, u0elo3]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h581, hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h583, hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h575, hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h580, hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h582, hlam, p626_0]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [h575, hc34, hlam, hphi, ht0b, ht45, ht5b, p626_1, u0elo3]
                        · have p626_0 := h626c.1
                          have p626_1 := h626c.2.1
                          have p626_2 := h626c.2.2.1
                          have p626_3 := h626c.2.2.2
                          linarith only [hlam, p626_0]
                    · linarith only [h0, h1, h574, h575, h578, h582, hlam, hphi, u0ehi6, u0elo2]
                  · linarith only [h554, h581, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h0, h1, h574, h575, h580, hlam, hphi, u0ehi6, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h673 | h673
            · linarith only [h0, h1, h554, h574, h673, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h675 | h675
              · linarith only [h0, h1, h575, h675, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h677 | h677
                · linarith only [h0, h1, h575, h675, h677, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                · linarith only [h0, h1, h677, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h680 | h680
          · rcases m.htr 1 2 3 (by decide) (by decide) with h681 | h681
            · linarith only [h0, h554, h681, hlam, hphi, u0ehi6, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h683 | h683
              · linarith only [h0, h572, h683, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h685 | h685
                · rcases m.htr 2 3 4 (by decide) (by decide) with h686 | h686
                  · linarith only [h574, h686, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · linarith only [h554, h686, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h1, h680, h685, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h690 | h690
            · linarith only [h554, h690, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h692 | h692
              · linarith only [h0, h1, h680, h692, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h694 | h694
                · linarith only [h0, h1, h680, h694, hc14, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h1, h694, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]

end R2N4
