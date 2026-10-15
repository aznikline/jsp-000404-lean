import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_M_LR_L_I_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
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
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h10, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h13, h6, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h13, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h16 | h16
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h17, h2, h8, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h19, h7, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h1, h16, h19, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h22 | h22
                    · linarith only [h22, h6, h8, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                      · linarith only [h0, h16, h24, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                        · linarith only [h0, h16, h2, h26, h4, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h2, h26, h4, h5, h6, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h0, h3, h6, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h30 | h30
              · linarith only [h0, h2, h30, h6, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h35 | h35
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h36 | h36
                        · linarith only [h0, h2, h32, h36, h6, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1, h33, h36, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h30, h33, h35, hlam]
                    · linarith only [h0, h2, h34, h4, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                      · linarith only [h0, h2, h33, h41, h42, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h0, h2, h30, h4, h42, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h32, h41, h6, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h46 | h46
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h47 | h47
                    · linarith only [h0, h2, h32, h47, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h2, h4, h47, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h50 | h50
                    · linarith only [h0, h2, h32, h50, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h2, h4, h50, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h53 | h53
            · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
              · rcases m.htr 1 3 4 (by decide) (by decide) with h55 | h55
                · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                  · linarith only [h5, h56, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                    · linarith only [h0, h53, h58, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h0, h53, h55, h58, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h61 | h61
                  · linarith only [h0, h2, h4, h5, h55, h61, hlam, hphi, u0ehi8, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h63 | h63
                    · linarith only [h0, h2, h55, h63, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h65 | h65
                      · linarith only [h0, h5, h54, h65, hlam, hphi, u0ehi8, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h67 | h67
                        · linarith only [h5, h67, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                        · rcases h4bigk with h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c | h69c
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [hlam, p69_0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h5, hc14, hc45, hlam, hphi, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h5, hc24, hc45, hlam, hphi, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h5, h53, h55, hc23, hc45, hlam, hphi, ht34, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h5, hlam, p69_0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h1, hlam, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [hlam, p69_0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h1, hc24, hlam, hphi, ht0b, ht45, ht5b, p69_1, u0elo0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h55, hlam, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h61, hlam, p69_0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h3, hlam, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h54, hlam, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [hlam, p69_0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h63, hlam, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h65, hlam, p69_0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h4, hlam, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h0, h2, h4, hc14, hlam, hphi, ht0b, ht45, ht5b, p69_1, u0elo0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h0, h2, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, p69_1, u0elo0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [hlam, p69_0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h67, hlam, p69_0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h0, h2, h4, h53, h55, hc23, hc45, hlam, hphi, ht34, p69_1, u0ehi8, u0elo0]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            rcases p69_3 (m.d 0 4) (by simp) with h91 | h91
                            · linarith only [h5, h91, hlam]
                            · linarith only [h1, h91, hlam]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            rcases p69_3 (m.d 0 4) (by simp) with h94 | h94
                            · linarith only [h5, h94, hlam]
                            · linarith only [h3, h94, hlam]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [h53, h55, hc23, hc45, hlam, hphi, ht34, p69_1]
                          · have p69_0 := h69c.1
                            have p69_1 := h69c.2.1
                            have p69_2 := h69c.2.2.1
                            have p69_3 := h69c.2.2.2
                            linarith only [hlam, p69_0]
              · linarith only [h0, h3, h53, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h100 | h100
              · linarith only [h0, h100, h2, h53, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                  · linarith only [h103, h5, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h105 | h105
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                      · linarith only [h0, h105, h106, h2, h5, hlam, hphi, u0ehi8, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h108 | h108
                        · linarith only [h0, h102, h108, h2, h5, h53, hlam, hphi, u0ehi8, u0elo0]
                        · rcases h4bigk with h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c | h110c
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h5, hc14, hc45, hlam, hphi, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h100, h5, hc12, hc45, hlam, hphi, ht23, ht34, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h5, hc34, hc45, hlam, hphi, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h5, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h1, hlam, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h100, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h1, hc34, hlam, hphi, ht0b, ht45, ht5b, p110_1, u0elo0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h103, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h3, hlam, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h0, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p110_1, u0elo0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h0, h105, h2, hc34, hlam, hphi, ht0b, ht45, ht5b, p110_1, u0elo0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h106, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h4, hlam, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h102, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h105, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h108, hlam, p110_0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h0, h100, h105, h2, hc12, hc45, hlam, hphi, ht23, ht34, p110_1, u0ehi8, u0elo0]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            rcases p110_3 (m.d 0 4) (by simp) with h132 | h132
                            · linarith only [h132, h5, hlam]
                            · linarith only [h1, h132, hlam]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [h100, hc12, hc45, hlam, hphi, ht23, ht34, p110_1]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            rcases p110_3 (m.d 0 4) (by simp) with h136 | h136
                            · linarith only [h136, h5, hlam]
                            · linarith only [h136, h4, hlam]
                          · have p110_0 := h110c.1
                            have p110_1 := h110c.2.1
                            have p110_2 := h110c.2.2.1
                            have p110_3 := h110c.2.2.2
                            linarith only [hlam, p110_0]
                    · linarith only [h0, h105, h2, h4, h53, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h141 | h141
                  · linarith only [h141, h5, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h143 | h143
                    · linarith only [h0, h102, h143, h2, h53, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h143, h2, h4, h53, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h146 | h146
          · rcases m.htr 1 2 3 (by decide) (by decide) with h147 | h147
            · rcases m.htr 1 2 4 (by decide) (by decide) with h148 | h148
              · rcases m.htr 1 3 4 (by decide) (by decide) with h149 | h149
                · linarith only [h149, h4, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h151 | h151
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h152 | h152
                    · linarith only [h0, h147, h152, h4, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h154 | h154
                      · linarith only [h0, h148, h154, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h0, h148, h151, h152, h154, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h157 | h157
                    · linarith only [h157, h4, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h159 | h159
                      · linarith only [h0, h149, h151, h159, h3, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h161 | h161
                        · rcases h4bigk with h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c | h162c
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [hlam, p162_0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            rcases p162_3 (m.d 0 4) (by simp) with h164 | h164
                            · rcases p162_3 (m.d 1 4) (by simp) with h165 | h165
                              · linarith only [h1, h165, hlam]
                              · rcases p162_3 (m.d 2 4) (by simp) with h167 | h167
                                · linarith only [h167, h3, hlam]
                                · rcases p162_3 (m.d 3 4) (by simp) with h169 | h169
                                  · rcases p162_3 (m.d 4 5) (by simp) with h170 | h170
                                    · linarith only [h146, h170, hlam]
                                    · linarith only [h151, h170, hlam]
                                  · linarith only [h149, h169, hlam]
                            · linarith only [h1, h164, hlam]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            rcases p162_3 (m.d 0 4) (by simp) with h175 | h175
                            · rcases p162_3 (m.d 1 4) (by simp) with h176 | h176
                              · linarith only [h1, h176, hlam]
                              · linarith only [h148, h176, hlam]
                            · linarith only [h175, h3, hlam]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h4, hlam, p162_0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h0, h147, h149, h151, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p162_1, u0elo0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h1, hlam, p162_1]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [hlam, p162_0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h151, hc24, hc45, hlam, hphi, p162_1]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h149, hlam, p162_1]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h151, hlam, p162_0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h3, hlam, p162_1]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h148, hlam, p162_1]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [hlam, p162_0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h157, hlam, p162_1]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h159, hlam, p162_0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p162_1, u0ehi8]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            rcases p162_3 (m.d 0 4) (by simp) with h193 | h193
                            · linarith only [h193, h4, hlam]
                            · linarith only [h1, h193, hlam]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            rcases p162_3 (m.d 0 4) (by simp) with h196 | h196
                            · linarith only [h196, h4, hlam]
                            · linarith only [h196, h3, hlam]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [hlam, p162_0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h147, h149, h151, hc23, hc34, hlam, hphi, p162_1]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h146, hlam, p162_0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h0, h146, h147, h149, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p162_1, u0elo0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h0, h146, h157, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p162_1, u0elo0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [h161, hlam, p162_0]
                          · have p162_0 := h162c.1
                            have p162_1 := h162c.2.1
                            have p162_2 := h162c.2.2.1
                            have p162_3 := h162c.2.2.2
                            linarith only [hlam, p162_0]
                        · linarith only [h0, h146, h161, h3, h4, hlam, hphi, u0ehi7, u0elo0]
              · linarith only [h0, h147, h148, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h208 | h208
              · linarith only [h0, h147, h2, h208, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h210 | h210
                · linarith only [h210, h4, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h213 | h213
                    · linarith only [h0, h2, h213, h4, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h215 | h215
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h216 | h216
                        · rcases h4bigk with h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c | h217c
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h0, h212, h3, hc45, hlam, hphi, ht0b, ht5b, p217_1, u0elo0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h0, h147, h213, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p217_1, u0elo0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h4, hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            rcases p217_3 (m.d 0 4) (by simp) with h222 | h222
                            · rcases p217_3 (m.d 1 4) (by simp) with h223 | h223
                              · linarith only [h1, h223, hlam]
                              · linarith only [h212, h223, hlam]
                            · linarith only [h222, hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h1, hlam, p217_1]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h208, hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h210, hlam, p217_1]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p217_1, u0elo0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h3, hlam, p217_1]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h0, h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p217_1, u0elo0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h213, hlam, p217_1]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h0, h3, hc45, hlam, hphi, ht0b, ht5b, p217_1, u0elo0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p217_1, u0ehi8]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            rcases p217_3 (m.d 0 4) (by simp) with h238 | h238
                            · linarith only [h238, h4, hlam]
                            · linarith only [h1, h238, hlam]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h147, h213, hc12, hc34, hlam, hphi, ht23, p217_1]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            rcases p217_3 (m.d 0 4) (by simp) with h243 | h243
                            · linarith only [h243, h4, hlam]
                            · linarith only [h146, h243, hlam]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h146, hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h212, hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h215, hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [h216, hlam, p217_0]
                          · have p217_0 := h217c.1
                            have p217_1 := h217c.2.1
                            have p217_2 := h217c.2.2.1
                            have p217_3 := h217c.2.2.2
                            linarith only [hlam, p217_0]
                        · linarith only [h1, h212, h216, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h208, h212, h215, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h253 | h253
                    · linarith only [h0, h146, h147, h210, h212, h253, h3, h4, hc12, hc23, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h255 | h255
                      · linarith only [h0, h147, h210, h212, h255, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h146, h147, h253, h255, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h258 | h258
            · rcases m.htr 1 2 4 (by decide) (by decide) with h259 | h259
              · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                · linarith only [h260, h4, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h262 | h262
                  · linarith only [h146, h262, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h258, h264, h4, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h266 | h266
                      · linarith only [h0, h146, h259, h266, h4, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h268 | h268
                        · linarith only [h146, h268, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                        · linarith only [h268, h4, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
              · linarith only [h0, h258, h259, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h272 | h272
              · linarith only [h0, h2, h258, h272, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
                · linarith only [h274, h4, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h276 | h276
                  · linarith only [h0, h146, h272, h276, h3, h4, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
                    · linarith only [h0, h2, h278, h4, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
                      · linarith only [h0, h146, h280, h3, h4, hlam, hphi, u0ehi7, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                        · linarith only [h0, h146, h258, h278, h282, h3, h4, hc12, hc34, hlam, hphi, ht23, u0ehi7, u0elo0]
                        · linarith only [h0, h258, h278, h282, h3, h4, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h285 | h285
        · linarith only [h2, h285, h3, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h287 | h287
          · rcases m.htr 1 2 3 (by decide) (by decide) with h288 | h288
            · rcases m.htr 1 2 4 (by decide) (by decide) with h289 | h289
              · linarith only [h0, h289, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h291 | h291
                · linarith only [h285, h291, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h293 | h293
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                    · linarith only [h1, h285, h288, h289, h294, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h296 | h296
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h297 | h297
                        · rcases h4bigk with h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c | h298c
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h288, h289, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p298_1, u0elo3]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h3, hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h285, hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            rcases p298_3 (m.d 0 4) (by simp) with h303 | h303
                            · rcases p298_3 (m.d 1 4) (by simp) with h304 | h304
                              · linarith only [h1, h304, hlam]
                              · linarith only [h293, h304, hlam]
                            · linarith only [h303, hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h1, hlam, p298_1]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h289, hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h291, hlam, p298_1]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p298_1, u0elo0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p298_1, u0ehi8]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h288, h289, h294, hc23, hc34, hlam, hphi, p298_1]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h294, hlam, p298_1]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            rcases p298_3 (m.d 0 4) (by simp) with h317 | h317
                            · linarith only [h3, h317, hlam]
                            · linarith only [h287, h317, hlam]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h2, h3, hc34, hlam, hphi, ht01, ht12, ht23, p298_1, u0ehi7]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h288, h289, hc23, hc34, hlam, hphi, p298_1]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h2, h3, hc34, hlam, hphi, ht01, ht12, ht23, p298_1, u0ehi7]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            rcases p298_3 (m.d 0 4) (by simp) with h324 | h324
                            · linarith only [h285, h324, hlam]
                            · linarith only [h287, h324, hlam]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h287, hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h293, hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h296, hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [h297, hlam, p298_0]
                          · have p298_0 := h298c.1
                            have p298_1 := h298c.2.1
                            have p298_2 := h298c.2.2.1
                            have p298_3 := h298c.2.2.2
                            linarith only [hlam, p298_0]
                        · linarith only [h2, h294, h297, h3, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                      · linarith only [h2, h293, h296, h3, hc14, hlam, hphi, ht01, u0ehi7]
                  · linarith only [h287, h288, h289, h293, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
            · linarith only [h2, h288, h3, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
            · rcases m.htr 1 2 4 (by decide) (by decide) with h337 | h337
              · linarith only [h0, h2, h3, h337, hlam, hphi, u0ehi7, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h339 | h339
                · linarith only [h285, h339, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h341 | h341
                  · linarith only [h1, h2, h287, h3, h341, hlam, hphi, u0ehi7, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h343 | h343
                    · linarith only [h1, h285, h336, h337, h343, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h345 | h345
                      · linarith only [h2, h287, h3, h345, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                      · linarith only [h2, h3, h345, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
            · linarith only [h2, h3, h336, hc12, hc24, hlam, hphi]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h349 | h349
      · rcases m.htr 0 3 4 (by decide) (by decide) with h350 | h350
        · rcases m.htr 0 4 5 (by decide) (by decide) with h351 | h351
          · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
            · linarith only [h2, h352, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h354 | h354
              · rcases m.htr 1 3 4 (by decide) (by decide) with h355 | h355
                · rcases m.htr 1 4 5 (by decide) (by decide) with h356 | h356
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h358 | h358
                      · linarith only [h0, h354, h358, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h0, h354, h356, h357, h358, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h2, h349, h351, h357, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h362 | h362
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h363 | h363
                      · linarith only [h354, h356, h363, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h365 | h365
                        · linarith only [h354, h356, h362, h365, hlam]
                        · rcases h4bigk with h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            rcases p367_3 (m.d 0 4) (by simp) with h369 | h369
                            · rcases p367_3 (m.d 1 4) (by simp) with h370 | h370
                              · linarith only [h1, h370, hlam]
                              · rcases p367_3 (m.d 2 4) (by simp) with h372 | h372
                                · linarith only [h349, h372, hlam]
                                · rcases p367_3 (m.d 3 4) (by simp) with h374 | h374
                                  · linarith only [h350, h374, hlam]
                                  · rcases p367_3 (m.d 4 5) (by simp) with h376 | h376
                                    · linarith only [h351, h376, hlam]
                                    · linarith only [h356, h376, hlam]
                            · linarith only [h1, h369, hlam]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            rcases p367_3 (m.d 0 4) (by simp) with h380 | h380
                            · rcases p367_3 (m.d 1 4) (by simp) with h381 | h381
                              · linarith only [h1, h381, hlam]
                              · linarith only [h354, h381, hlam]
                            · linarith only [h349, h380, hlam]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            rcases p367_3 (m.d 0 4) (by simp) with h385 | h385
                            · rcases p367_3 (m.d 1 4) (by simp) with h386 | h386
                              · linarith only [h1, h386, hlam]
                              · linarith only [h355, h386, hlam]
                            · linarith only [h350, h385, hlam]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h349, h354, h356, h362, hc34, hlam, hphi, ht0b, ht45, ht5b, p367_1, u0elo1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h1, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h356, h362, hc34, hc45, hlam, hphi, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h0, h354, hc34, hlam, hphi, ht0b, ht45, ht5b, p367_1, u0elo0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h356, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h349, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h354, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h2, h349, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h363, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h350, hlam, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h355, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h362, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h365, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h351, hlam, p367_0]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h2, h349, h351, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h2, h349, h351, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [h2, h349, h351, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p367_1]
                          · have p367_0 := h367c.1
                            have p367_1 := h367c.2.1
                            have p367_2 := h367c.2.2.1
                            have p367_3 := h367c.2.2.2
                            linarith only [hlam, p367_0]
                    · linarith only [h2, h349, h351, h356, h362, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h350, h352, h354, h355, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h2, h349, h354, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h414 | h414
            · linarith only [h2, h414, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h416 | h416
              · rcases m.htr 1 3 4 (by decide) (by decide) with h417 | h417
                · rcases m.htr 1 4 5 (by decide) (by decide) with h418 | h418
                  · linarith only [h351, h418, hc14, hlam, hphi, ht01, u0ehi8]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h421 | h421
                      · linarith only [h0, h351, h416, h421, hlam, hphi, u0ehi8, u0elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h423 | h423
                        · linarith only [h0, h351, h416, h420, h423, hlam, hphi, u0ehi8, u0elo0]
                        · rcases h4bigk with h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c | h425c
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h351, hc14, hc45, hlam, hphi, p425_1]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h351, hc24, hc45, hlam, hphi, p425_1]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h351, hc34, hc45, hlam, hphi, p425_1]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h351, hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h1, hlam, p425_1]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h1, h420, hc34, hlam, hphi, ht0b, ht45, ht5b, p425_1, u0elo0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h0, h416, hc34, hlam, hphi, ht0b, ht45, ht5b, p425_1, u0elo0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h418, hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h349, hlam, p425_1]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h416, hlam, p425_1]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h2, h349, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p425_1]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h421, hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h350, hlam, p425_1]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h417, hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h420, hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [h423, hlam, p425_0]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p425_1, u0ehi8]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            rcases p425_3 (m.d 0 4) (by simp) with h447 | h447
                            · linarith only [h351, h447, hlam]
                            · linarith only [h1, h447, hlam]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            rcases p425_3 (m.d 0 4) (by simp) with h450 | h450
                            · linarith only [h351, h450, hlam]
                            · linarith only [h349, h450, hlam]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            rcases p425_3 (m.d 0 4) (by simp) with h453 | h453
                            · linarith only [h351, h453, hlam]
                            · linarith only [h350, h453, hlam]
                          · have p425_0 := h425c.1
                            have p425_1 := h425c.2.1
                            have p425_2 := h425c.2.2.1
                            have p425_3 := h425c.2.2.2
                            linarith only [hlam, p425_0]
                    · linarith only [h2, h420, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h350, h414, h416, h417, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
              · linarith only [h2, h349, h416, hc12, hc23, hlam, hphi]
        · linarith only [h2, h349, h350, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h461 | h461
        · rcases m.htr 0 4 5 (by decide) (by decide) with h462 | h462
          · rcases m.htr 1 2 3 (by decide) (by decide) with h463 | h463
            · linarith only [h2, h463, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h465 | h465
              · linarith only [h0, h349, h465, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
                · rcases m.htr 1 4 5 (by decide) (by decide) with h468 | h468
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h469 | h469
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h470 | h470
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h471 | h471
                        · rcases h4bigk with h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c | h472c
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h461, h467, h471, hc45, hlam, hphi, ht0b, ht5b, p472_1, u0elo2]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h349, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h461, h471, hc45, hlam, hphi, ht0b, ht5b, p472_1, u0elo2]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            rcases p472_3 (m.d 0 4) (by simp) with h477 | h477
                            · rcases p472_3 (m.d 1 4) (by simp) with h478 | h478
                              · linarith only [h1, h478, hlam]
                              · linarith only [h468, h478, hlam]
                            · linarith only [h477, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h1, hlam, p472_1]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h465, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h1, h471, hc45, hlam, hphi, ht0b, ht5b, p472_1, u0elo0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p472_1, u0elo0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h469, hc23, hlam, hphi, ht01, ht12, p472_1, u0ehi8]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            rcases p472_3 (m.d 0 4) (by simp) with h488 | h488
                            · linarith only [h349, h488, hlam]
                            · linarith only [h1, h488, hlam]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            rcases p472_3 (m.d 0 4) (by simp) with h492 | h492
                            · linarith only [h349, h492, hlam]
                            · linarith only [h461, h492, hlam]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            rcases p472_3 (m.d 0 4) (by simp) with h495 | h495
                            · linarith only [h349, h495, hlam]
                            · linarith only [h462, h495, hlam]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h461, hlam, p472_1]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h467, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h469, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h1, h467, hc45, hlam, hphi, ht0b, ht5b, p472_1, u0elo0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h462, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h468, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h470, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [h471, hlam, p472_0]
                          · have p472_0 := h472c.1
                            have p472_1 := h472c.2.1
                            have p472_2 := h472c.2.2.1
                            have p472_3 := h472c.2.2.2
                            linarith only [hlam, p472_0]
                        · linarith only [h1, h468, h471, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h1, h468, h470, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h2, h469, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h511 | h511
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h512 | h512
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h513 | h513
                        · linarith only [h461, h465, h468, h513, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases h4bigk with h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c | h515c
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            rcases p515_3 (m.d 0 4) (by simp) with h517 | h517
                            · rcases p515_3 (m.d 1 4) (by simp) with h518 | h518
                              · linarith only [h1, h518, hlam]
                              · rcases p515_3 (m.d 2 4) (by simp) with h520 | h520
                                · rcases p515_3 (m.d 3 4) (by simp) with h521 | h521
                                  · linarith only [h461, h521, hlam]
                                  · rcases p515_3 (m.d 4 5) (by simp) with h523 | h523
                                    · linarith only [h462, h523, hlam]
                                    · linarith only [h468, h523, hlam]
                                · linarith only [h465, h520, hlam]
                            · linarith only [h1, h517, hlam]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h349, hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            rcases p515_3 (m.d 0 4) (by simp) with h529 | h529
                            · rcases p515_3 (m.d 1 4) (by simp) with h530 | h530
                              · linarith only [h1, h530, hlam]
                              · linarith only [h467, h530, hlam]
                            · linarith only [h461, h529, hlam]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h1, h465, h468, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p515_1, u0elo0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h1, hlam, p515_1]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h465, hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h468, hc34, hc45, hlam, hphi, p515_1]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h468, hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h511, hc23, hlam, hphi, ht01, ht12, p515_1, u0ehi8]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            rcases p515_3 (m.d 0 4) (by simp) with h541 | h541
                            · linarith only [h349, h541, hlam]
                            · linarith only [h1, h541, hlam]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            rcases p515_3 (m.d 0 4) (by simp) with h545 | h545
                            · linarith only [h349, h545, hlam]
                            · linarith only [h461, h545, hlam]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h465, h468, hc12, hc24, hlam, hphi, p515_1]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h461, hlam, p515_1]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h467, hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h511, hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h513, hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h462, hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h1, h462, h465, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p515_1, u0elo0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h512, hlam, p515_0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [h1, h462, hc34, hlam, hphi, ht0b, ht45, ht5b, p515_1, u0elo0]
                          · have p515_0 := h515c.1
                            have p515_1 := h515c.2.1
                            have p515_2 := h515c.2.2.1
                            have p515_3 := h515c.2.2.2
                            linarith only [hlam, p515_0]
                      · linarith only [h1, h349, h462, h512, hlam, hphi, u0ehi6, u0elo0]
                    · linarith only [h2, h467, h511, hc13, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h561 | h561
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h562 | h562
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h563 | h563
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h564 | h564
                        · rcases h4bigk with h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h1, h561, hc45, hlam, hphi, ht0b, ht5b, p565_1, u0elo0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h349, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h1, h463, h467, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p565_1, u0elo0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            rcases p565_3 (m.d 0 4) (by simp) with h570 | h570
                            · rcases p565_3 (m.d 1 4) (by simp) with h571 | h571
                              · linarith only [h1, h571, hlam]
                              · linarith only [h561, h571, hlam]
                            · linarith only [h570, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h1, hlam, p565_1]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h465, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h467, hlam, p565_1]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h1, hc45, hlam, hphi, ht0b, ht5b, p565_1, u0elo0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hc24, hlam, hphi, ht01, ht12, p565_1, u0ehi8]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            rcases p565_3 (m.d 0 4) (by simp) with h581 | h581
                            · linarith only [h349, h581, hlam]
                            · linarith only [h1, h581, hlam]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h463, h467, h562, hc12, hc23, hlam, hphi, p565_1]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            rcases p565_3 (m.d 0 4) (by simp) with h586 | h586
                            · linarith only [h349, h586, hlam]
                            · linarith only [h462, h586, hlam]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h461, hlam, p565_1]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h461, hc14, hlam, hphi, ht0b, ht45, ht5b, p565_1, u0elo2]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h562, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h461, hc45, hlam, hphi, ht0b, ht5b, p565_1, u0elo2]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h462, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h561, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h563, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h564, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                        · linarith only [h1, h561, h564, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h461, h467, h561, h563, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                    · linarith only [h2, h461, h562, hlam, hphi, u0ehi6, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h602 | h602
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h603 | h603
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h604 | h604
                        · linarith only [h461, h561, h604, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h1, h462, h463, h467, h604, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1, h349, h462, h603, hlam, hphi, u0ehi6, u0elo0]
                    · linarith only [h2, h602, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h609 | h609
            · linarith only [h2, h609, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h611 | h611
              · linarith only [h0, h349, h611, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h613 | h613
                · rcases m.htr 1 4 5 (by decide) (by decide) with h614 | h614
                  · linarith only [h1, h462, h614, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h616 | h616
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h617 | h617
                      · linarith only [h349, h462, h616, h617, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h349, h617, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h2, h613, h616, hc13, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h621 | h621
                  · linarith only [h349, h461, h462, h613, h621, hlam, hphi, u0ehi6, u0elo2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h623 | h623
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h624 | h624
                      · linarith only [h349, h462, h624, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                      · linarith only [h349, h624, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                    · linarith only [h2, h461, h623, hlam, hphi, u0ehi6, u0elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h628 | h628
          · rcases m.htr 1 2 3 (by decide) (by decide) with h629 | h629
            · linarith only [h2, h629, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h631 | h631
              · linarith only [h0, h349, h631, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h633 | h633
                · linarith only [h2, h461, h633, hc13, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h635 | h635
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h636 | h636
                    · linarith only [h2, h461, h636, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h2, h636, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h639 | h639
                    · linarith only [h1, h2, h461, h628, h629, h633, h635, h639, hc12, hc23, hlam, hphi, u0ehi6, u0elo0]
                    · linarith only [h1, h2, h628, h629, h633, h635, h639, hc12, hc34, hlam, hphi, ht23, u0ehi6, u0elo0]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
            · linarith only [h2, h642, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h644 | h644
              · linarith only [h0, h349, h644, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h646 | h646
                · linarith only [h2, h461, h646, hc13, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h648 | h648
                  · linarith only [h1, h628, h648, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h650 | h650
                    · linarith only [h2, h461, h650, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h2, h650, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h653 | h653
    · rcases m.htr 0 2 4 (by decide) (by decide) with h654 | h654
      · linarith only [h0, h1, h654, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h656 | h656
        · linarith only [h0, h1, h653, h656, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
          · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
            · rcases m.htr 1 2 4 (by decide) (by decide) with h660 | h660
              · linarith only [h0, h1, h654, h660, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h662 | h662
                · linarith only [h0, h1, h656, h659, h660, h662, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                · linarith only [h0, h1, h659, h662, hc23, hc34, hlam, hphi]
            · linarith only [h653, h654, h659, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h666 | h666
            · linarith only [h0, h1, h658, h666, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h1, h653, h658, h666, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h669 | h669
      · linarith only [h0, h1, h669, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h671 | h671
        · rcases m.htr 0 4 5 (by decide) (by decide) with h672 | h672
          · rcases m.htr 1 2 3 (by decide) (by decide) with h673 | h673
            · linarith only [h653, h673, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h675 | h675
              · linarith only [h0, h669, h675, hlam, hphi, u0ehi6, u0elo0]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h677 | h677
                · rcases m.htr 1 4 5 (by decide) (by decide) with h678 | h678
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h679 | h679
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h680 | h680
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h681 | h681
                        · rcases h4bigk with h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c | h682c
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h1, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h669, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h671, h681, hc45, hlam, hphi, ht0b, ht5b, p682_1, u0elo2]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            rcases p682_3 (m.d 0 4) (by simp) with h687 | h687
                            · rcases p682_3 (m.d 1 4) (by simp) with h688 | h688
                              · rcases p682_3 (m.d 2 4) (by simp) with h689 | h689
                                · rcases p682_3 (m.d 3 4) (by simp) with h690 | h690
                                  · linarith only [h671, h690, hlam]
                                  · linarith only [h681, h690, hlam]
                                · linarith only [h680, h689, hlam]
                              · linarith only [h678, h688, hlam]
                            · linarith only [h687, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h673, h677, hc23, hlam, hphi, ht01, ht12, p682_1, u0ehi8]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h675, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            rcases p682_3 (m.d 0 4) (by simp) with h699 | h699
                            · linarith only [h1, h699, hlam]
                            · linarith only [h671, h699, hlam]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            rcases p682_3 (m.d 0 4) (by simp) with h702 | h702
                            · linarith only [h1, h702, hlam]
                            · linarith only [h672, h702, hlam]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h0, h1, h679, hc12, hc23, hlam, hphi, p682_1]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h0, h1, h679, hc23, hlam, hphi, ht01, ht12, p682_1, u0ehi6]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            rcases p682_3 (m.d 0 4) (by simp) with h708 | h708
                            · linarith only [h669, h708, hlam]
                            · linarith only [h671, h708, hlam]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            rcases p682_3 (m.d 0 4) (by simp) with h711 | h711
                            · linarith only [h669, h711, hlam]
                            · linarith only [h672, h711, hlam]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h671, hlam, p682_1]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h677, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h679, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h671, hc45, hlam, hphi, ht0b, ht5b, p682_1, u0elo2]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h672, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h678, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h680, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [h681, hlam, p682_0]
                          · have p682_0 := h682c.1
                            have p682_1 := h682c.2.1
                            have p682_2 := h682c.2.2.1
                            have p682_3 := h682c.2.2.2
                            linarith only [hlam, p682_0]
                        · rcases h4bigk with h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c | h724c
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h1, hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h669, hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            rcases p724_3 (m.d 0 4) (by simp) with h728 | h728
                            · rcases p724_3 (m.d 1 4) (by simp) with h729 | h729
                              · rcases p724_3 (m.d 2 4) (by simp) with h730 | h730
                                · rcases p724_3 (m.d 3 4) (by simp) with h731 | h731
                                  · linarith only [h671, h731, hlam]
                                  · rcases p724_3 (m.d 4 5) (by simp) with h733 | h733
                                    · linarith only [h672, h733, hlam]
                                    · linarith only [h681, h733, hlam]
                                · linarith only [h679, h730, hlam]
                              · linarith only [h677, h729, hlam]
                            · linarith only [h671, h728, hlam]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h681, hc34, hlam, hphi, ht0b, ht45, ht5b, p724_1, u0elo3]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [hc14, hlam, hphi, ht01, p724_1, u0ehi8]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h675, hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            rcases p724_3 (m.d 0 4) (by simp) with h743 | h743
                            · linarith only [h1, h743, hlam]
                            · linarith only [h671, h743, hlam]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            rcases p724_3 (m.d 0 4) (by simp) with h746 | h746
                            · linarith only [h1, h746, hlam]
                            · linarith only [h672, h746, hlam]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h0, h1, h679, hc23, hlam, hphi, ht01, ht12, p724_1, u0ehi6]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h0, h1, h679, hc23, hlam, hphi, ht01, ht12, p724_1, u0ehi6]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            rcases p724_3 (m.d 0 4) (by simp) with h752 | h752
                            · linarith only [h669, h752, hlam]
                            · linarith only [h671, h752, hlam]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            rcases p724_3 (m.d 0 4) (by simp) with h755 | h755
                            · linarith only [h669, h755, hlam]
                            · linarith only [h672, h755, hlam]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h671, hlam, p724_1]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h677, hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h679, hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h681, hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h672, hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h678, hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h680, hlam, p724_0]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [h672, hc34, hlam, hphi, ht0b, ht45, ht5b, p724_1, u0elo3]
                          · have p724_0 := h724c.1
                            have p724_1 := h724c.2.1
                            have p724_2 := h724c.2.2.1
                            have p724_3 := h724c.2.2.2
                            linarith only [hlam, p724_0]
                      · linarith only [h0, h1, h671, h672, h675, h680, hlam, hphi, u0ehi6, u0elo2]
                    · linarith only [h653, h679, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h0, h1, h671, h672, h678, hlam, hphi, u0ehi6, u0elo2]
                · linarith only [h0, h1, h671, h677, hlam, hphi, u0ehi6, u0elo2]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h772 | h772
            · linarith only [h653, h772, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h774 | h774
              · linarith only [h0, h1, h672, h774, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h776 | h776
                · rcases m.htr 1 4 5 (by decide) (by decide) with h777 | h777
                  · linarith only [h0, h1, h672, h776, h777, hc13, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h1, h777, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                · linarith only [h0, h1, h671, h776, hlam, hphi, u0ehi6, u0elo2]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
          · rcases m.htr 1 2 3 (by decide) (by decide) with h782 | h782
            · linarith only [h0, h653, h782, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
              · linarith only [h0, h1, h669, h784, hc14, hlam, hphi, ht01, u0ehi6]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h786 | h786
                · linarith only [h671, h786, hc13, hlam, hphi, ht01, u0ehi7]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h788 | h788
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h789 | h789
                    · linarith only [h0, h1, h786, h789, hc12, hc23, hlam, hphi]
                    · linarith only [h653, h789, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h0, h1, h781, h788, hlam, hphi, u0ehi6, u0elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h793 | h793
            · linarith only [h653, h793, hc12, hlam, hphi, ht01, u0ehi6]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h795 | h795
              · linarith only [h0, h1, h781, h795, hc24, hc45, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h797 | h797
                · linarith only [h653, h671, h797, hc13, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h799 | h799
                  · linarith only [h0, h1, h781, h799, hc14, hlam, hphi, ht01, u0ehi6]
                  · linarith only [h0, h1, h799, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]

end R2N4
