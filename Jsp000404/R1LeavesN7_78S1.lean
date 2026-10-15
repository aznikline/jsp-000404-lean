import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_L_R_L_0_L_I (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
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
  have h0ehi := hb0.1
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16 | h16
                                  · linarith only [h0, h13, h16, h8, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                  · linarith only [h0, h13, h15, h16, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                                  · linarith only [h15, h19, h3, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
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
                                      linarith only [h14, h3, h8, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p21_1, u2elo0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h14, h3, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p21_1, u2elo0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      rcases p21_3 (m.d 0 3) (by simp) with h25 | h25
                                      · rcases p21_3 (m.d 1 3) (by simp) with h26 | h26
                                        · linarith only [h1, h26, hlam]
                                        · linarith only [h11, h26, hlam]
                                      · linarith only [h25, hlam, p21_0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      rcases p21_3 (m.d 0 3) (by simp) with h30 | h30
                                      · rcases p21_3 (m.d 1 3) (by simp) with h31 | h31
                                        · linarith only [h1, h31, hlam]
                                        · linarith only [h12, h31, hlam]
                                      · linarith only [h30, hlam, p21_0]
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
                                      linarith only [h1, h14, h19, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      rcases p21_3 (m.d 0 3) (by simp) with h38 | h38
                                      · rcases p21_3 (m.d 1 3) (by simp) with h39 | h39
                                        · rcases p21_3 (m.d 2 3) (by simp) with h40 | h40
                                          · linarith only [h40, h8, hlam]
                                          · linarith only [h13, h40, hlam]
                                        · linarith only [h39, hlam, p21_0]
                                      · linarith only [h38, h5, hlam]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      rcases p21_3 (m.d 0 3) (by simp) with h45 | h45
                                      · rcases p21_3 (m.d 1 3) (by simp) with h46 | h46
                                        · rcases p21_3 (m.d 2 3) (by simp) with h47 | h47
                                          · linarith only [h47, h8, hlam]
                                          · linarith only [h14, h47, hlam]
                                        · linarith only [h46, hlam, p21_0]
                                      · linarith only [h45, h6, hlam]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h3, hlam, p21_0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h8, hlam, p21_0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [hlam, p21_0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21_1, u2elo0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h0, h19, h8, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21_1, u2elo0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h5, hlam, p21_0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h11, hlam, p21_0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h13, hlam, p21_0]
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
                                      linarith only [h6, hlam, p21_0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h12, hlam, p21_0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h14, hlam, p21_0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21_1, u2elo0]
                                    · have p21_0 := h21c.1
                                      have p21_1 := h21c.2.1
                                      have p21_2 := h21c.2.2.1
                                      have p21_3 := h21c.2.2.2
                                      linarith only [hlam, p21_0]
                              · linarith only [h1, h12, h13, h14, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h68 | h68
                              · linarith only [h13, h3, h5, h68, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h71 | h71
                                  · rcases h3bigk with h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c | h72c
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h11, h3, h68, h71, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      rcases p72_3 (m.d 0 3) (by simp) with h75 | h75
                                      · rcases p72_3 (m.d 1 3) (by simp) with h76 | h76
                                        · linarith only [h1, h76, hlam]
                                        · linarith only [h76, h8, hlam]
                                      · linarith only [h3, h75, hlam]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h3, h68, h71, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h3, h68, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h1, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      rcases p72_3 (m.d 0 3) (by simp) with h84 | h84
                                      · rcases p72_3 (m.d 1 3) (by simp) with h85 | h85
                                        · rcases p72_3 (m.d 2 3) (by simp) with h86 | h86
                                          · linarith only [h8, h86, hlam]
                                          · rcases p72_3 (m.d 3 4) (by simp) with h88 | h88
                                            · linarith only [h11, h88, hlam]
                                            · linarith only [h13, h88, hlam]
                                        · linarith only [h8, h85, hlam]
                                      · linarith only [h3, h84, hlam]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h1, h68, h71, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h1, h3, h68, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h3, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h8, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h13, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h68, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h5, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h11, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h1, h11, h3, h68, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h6, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h12, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h71, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [hlam, p72_0]
                                  · linarith only [h4, h70, h71, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h111 | h111
                                  · linarith only [h1, h11, h111, h3, h70, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                  · linarith only [h111, h13, h3, h5, h7, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · linarith only [h11, h12, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h115 | h115
                          · linarith only [h11, h115, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                            · linarith only [h11, h117, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                              · linarith only [h11, h115, h119, h3, h5, h8, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h121 | h121
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h122 | h122
                                  · rcases h3bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      rcases p123_3 (m.d 0 3) (by simp) with h125 | h125
                                      · rcases p123_3 (m.d 1 3) (by simp) with h126 | h126
                                        · linarith only [h1, h126, hlam]
                                        · rcases p123_3 (m.d 2 3) (by simp) with h128 | h128
                                          · linarith only [h128, h3, hlam]
                                          · rcases p123_3 (m.d 3 4) (by simp) with h130 | h130
                                            · linarith only [h130, h5, hlam]
                                            · linarith only [h11, h130, hlam]
                                      · linarith only [h1, h125, hlam]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      rcases p123_3 (m.d 0 3) (by simp) with h134 | h134
                                      · rcases p123_3 (m.d 1 3) (by simp) with h135 | h135
                                        · linarith only [h1, h135, hlam]
                                        · linarith only [h135, h8, hlam]
                                      · linarith only [h134, h3, hlam]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h115, h122, h3, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p123_1, u2elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h115, h3, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p123_1, u2elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h1, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h115, h122, hc23, hc34, hlam, hphi, p123_1]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h11, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h115, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h3, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h8, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h117, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h119, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h5, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h3, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p123_1, u2elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p123_1, u2elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p123_1, u2elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h6, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h3, h6, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p123_1, u2elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p123_1, u2elo0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [h122, hlam, p123_0]
                                    · have p123_0 := h123c.1
                                      have p123_1 := h123c.2.1
                                      have p123_2 := h123c.2.2.1
                                      have p123_3 := h123c.2.2.2
                                      linarith only [hlam, p123_0]
                                  · linarith only [h121, h122, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h162 | h162
                                  · linarith only [h121, h162, h3, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                  · linarith only [h11, h162, h3, h5, h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h165 | h165
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h166 | h166
                          · linarith only [h10, h166, h8, hlam]
                          · linarith only [h165, h166, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h169 | h169
                          · linarith only [h165, h169, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h171 | h171
                            · linarith only [h165, h171, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h173 | h173
                              · linarith only [h10, h169, h173, h3, hc12, hlam, hphi, u2elo0]
                              · linarith only [h10, h171, h173, h3, h6, h9, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h4, h9, hc12, hlam, hphi, u2elo0]
                  · linarith only [h3, h8, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h178 | h178
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h179 | h179
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h180 | h180
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h181 | h181
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h182 | h182
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h183 | h183
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h184 | h184
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                                · linarith only [h179, h181, h185, h7, hc13, hlam, hphi, ht01, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h187 | h187
                                  · linarith only [h178, h183, h187, h7, hc12, hlam, hphi, ht01, u0ehi3]
                                  · rcases h3bigk with h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c | h189c
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h178, h184, h187, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p189_1, u2elo0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h184, h187, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p189_1, u2elo0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      rcases p189_3 (m.d 0 3) (by simp) with h193 | h193
                                      · rcases p189_3 (m.d 1 3) (by simp) with h194 | h194
                                        · linarith only [h1, h194, hlam]
                                        · linarith only [h181, h194, hlam]
                                      · linarith only [h193, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      rcases p189_3 (m.d 0 3) (by simp) with h198 | h198
                                      · rcases p189_3 (m.d 1 3) (by simp) with h199 | h199
                                        · linarith only [h1, h199, hlam]
                                        · linarith only [h182, h199, hlam]
                                      · linarith only [h198, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h1, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h1, h184, h187, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p189_1]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      rcases p189_3 (m.d 0 3) (by simp) with h206 | h206
                                      · rcases p189_3 (m.d 1 3) (by simp) with h207 | h207
                                        · rcases p189_3 (m.d 2 3) (by simp) with h208 | h208
                                          · linarith only [h178, h208, hlam]
                                          · linarith only [h183, h208, hlam]
                                        · linarith only [h207, hlam, p189_0]
                                      · linarith only [h206, h5, hlam]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      rcases p189_3 (m.d 0 3) (by simp) with h213 | h213
                                      · rcases p189_3 (m.d 1 3) (by simp) with h214 | h214
                                        · rcases p189_3 (m.d 2 3) (by simp) with h215 | h215
                                          · linarith only [h178, h215, hlam]
                                          · linarith only [h184, h215, hlam]
                                        · linarith only [h214, hlam, p189_0]
                                      · linarith only [h213, h6, hlam]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h3, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h178, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p189_1, u2elo0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h0, h178, h187, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p189_1, u2elo0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h5, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h181, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h183, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h187, hlam, p189_1]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h6, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h182, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h184, hlam, p189_0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p189_1, u2elo0]
                                    · have p189_0 := h189c.1
                                      have p189_1 := h189c.2.1
                                      have p189_2 := h189c.2.2.1
                                      have p189_3 := h189c.2.2.2
                                      linarith only [hlam, p189_0]
                              · linarith only [h1, h182, h183, h184, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                              · linarith only [h183, h236, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h238 | h238
                                · linarith only [h238, h7, hlam, hphi, ht01, ht12, u0ehi3, u2elo3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h240 | h240
                                  · linarith only [h1, h181, h240, h3, h7, hlam, hphi, ht01, ht12, u0ehi3, u2elo0]
                                  · rcases h3bigk with h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c | h242c
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h182, h183, h240, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p242_1, u2elo0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      rcases p242_3 (m.d 0 3) (by simp) with h245 | h245
                                      · rcases p242_3 (m.d 1 3) (by simp) with h246 | h246
                                        · linarith only [h1, h246, hlam]
                                        · linarith only [h178, h246, hlam]
                                      · linarith only [h245, h3, hlam]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h183, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p242_1, u2elo0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h183, h240, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p242_1, u2elo0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h1, hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      rcases p242_3 (m.d 0 3) (by simp) with h254 | h254
                                      · rcases p242_3 (m.d 1 3) (by simp) with h255 | h255
                                        · rcases p242_3 (m.d 2 3) (by simp) with h256 | h256
                                          · linarith only [h178, h256, hlam]
                                          · rcases p242_3 (m.d 3 4) (by simp) with h258 | h258
                                            · linarith only [h181, h258, hlam]
                                            · linarith only [h183, h258, hlam]
                                        · linarith only [h178, h255, hlam]
                                      · linarith only [h254, h3, hlam]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h1, h183, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p242_1]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h1, h183, h240, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p242_1, u2elo0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h3, hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h178, hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h183, hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h236, hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h5, hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h181, hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p242_1, u2elo0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h240, hlam, p242_1]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h6, hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h182, hlam, p242_0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h1, h182, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p242_1, u2elo0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [h1, h182, h183, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p242_1, u2elo0]
                                    · have p242_0 := h242c.1
                                      have p242_1 := h242c.2.1
                                      have p242_2 := h242c.2.2.1
                                      have p242_3 := h242c.2.2.2
                                      linarith only [hlam, p242_0]
                          · linarith only [h181, h182, h3, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h281 | h281
                          · linarith only [h181, h281, h3, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h283 | h283
                            · linarith only [h181, h283, h3, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h285 | h285
                              · linarith only [h178, h181, h281, h285, h3, h5, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h287 | h287
                                · linarith only [h179, h287, h7, hc14, hlam, hphi, ht01, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h289 | h289
                                  · linarith only [h289, h3, h5, h7, hlam, hphi, ht01, ht12, u0ehi3, u2elo0]
                                  · rcases h3bigk with h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c | h291c
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      rcases p291_3 (m.d 0 3) (by simp) with h293 | h293
                                      · rcases p291_3 (m.d 1 3) (by simp) with h294 | h294
                                        · linarith only [h1, h294, hlam]
                                        · rcases p291_3 (m.d 2 3) (by simp) with h296 | h296
                                          · linarith only [h296, h3, hlam]
                                          · rcases p291_3 (m.d 3 4) (by simp) with h298 | h298
                                            · linarith only [h298, h5, hlam]
                                            · linarith only [h181, h298, hlam]
                                      · linarith only [h1, h293, hlam]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      rcases p291_3 (m.d 0 3) (by simp) with h302 | h302
                                      · rcases p291_3 (m.d 1 3) (by simp) with h303 | h303
                                        · linarith only [h1, h303, hlam]
                                        · linarith only [h178, h303, hlam]
                                      · linarith only [h3, h302, hlam]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h178, h181, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p291_1, u2elo0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h178, h281, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p291_1, u2elo0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h1, hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h181, hc23, hc34, hlam, hphi, p291_1]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h181, hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h281, hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h3, hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h178, hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h283, hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h285, hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h5, hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h3, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p291_1, u2elo0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p291_1, u2elo0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h289, hlam, p291_1]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h6, hlam, p291_0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h178, h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p291_1, u2elo0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h3, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p291_1, u2elo0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [h181, h3, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p291_1, u2elo0]
                                    · have p291_0 := h291c.1
                                      have p291_1 := h291c.2.1
                                      have p291_2 := h291c.2.2.1
                                      have p291_3 := h291c.2.2.2
                                      linarith only [hlam, p291_0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h329 | h329
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h330 | h330
                          · linarith only [h178, h180, h330, hlam]
                          · linarith only [h3, h329, h330, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h333 | h333
                          · linarith only [h3, h329, h333, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h335 | h335
                            · linarith only [h3, h329, h335, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h337 | h337
                              · linarith only [h180, h3, h333, h337, hc12, hlam, hphi, u2elo0]
                              · linarith only [h179, h180, h3, h335, h337, h6, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h178, h179, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h178, h3, hc12, hlam, hphi, u2elo0]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h342 | h342
                · linarith only [h342, h5, h6, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h344 | h344
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h345 | h345
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h346 | h346
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h347 | h347
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h348 | h348
                          · linarith only [h344, h348, h6, hc12, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h351 | h351
                              · linarith only [h351, h5, h6, hlam, hphi, ht01, ht12, u0ehi3, u2elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h353 | h353
                                · linarith only [h342, h344, h350, h353, hc13, hlam, hphi, ht01, u0ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h355 | h355
                                  · linarith only [h342, h355, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
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
                                      linarith only [h355, h6, hc13, hc45, hlam, hphi, ht34, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h355, h6, hc23, hc45, hlam, hphi, ht34, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h355, h6, hc34, hc45, hlam, hphi, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h6, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h1, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h1, h350, h355, h5, h6, hc01, hc34, hc45, hlam, hphi, p357_1, u0ehi3]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h1, h355, h6, hc34, hc45, hlam, hphi, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h348, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h3, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h344, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h3, h355, h5, h6, hc34, hc45, hlam, hphi, ht01, ht12, p357_1, u0ehi3, u2elo0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h351, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h5, hlam, p357_0]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h347, hlam, p357_0]
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
                                      linarith only [h355, hlam, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h355, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p357_1, u0ehi3]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h347, h355, hc34, hc45, hlam, hphi, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [h350, h355, hc34, hc45, hlam, hphi, p357_1]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      rcases p357_3 (m.d 0 3) (by simp) with h381 | h381
                                      · linarith only [h381, h6, hlam]
                                      · linarith only [h381, h5, hlam]
                                    · have p357_0 := h357c.1
                                      have p357_1 := h357c.2.1
                                      have p357_2 := h357c.2.2.1
                                      have p357_3 := h357c.2.2.2
                                      linarith only [hlam, p357_0]
                            · linarith only [h350, h5, h6, hc23, hc35, hlam, hphi]
                        · linarith only [h344, h347, h5, h6, hc23, hc35, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h387 | h387
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h388 | h388
                          · linarith only [h388, h6, hc13, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h390 | h390
                            · linarith only [h344, h346, h390, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                            · linarith only [h390, h5, h6, hc23, hc35, hlam, hphi]
                        · linarith only [h387, h5, h6, hc13, hc35, hlam, hphi]
                    · linarith only [h345, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h3, h344, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h396 | h396
              · rcases m.htr 0 4 5 (by decide) (by decide) with h397 | h397
                · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h399 | h399
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h400 | h400
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                        · linarith only [h401, h5, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h403 | h403
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                            · linarith only [h396, h404, h5, hlam, hphi, ht01, ht12, u0ehi4, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h406 | h406
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h407 | h407
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h408 | h408
                                  · rcases h3bigk with h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c | h409c
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h5, hc13, hc34, hlam, hphi, p409_1]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h406, h408, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p409_1]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h5, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      rcases p409_3 (m.d 0 3) (by simp) with h414 | h414
                                      · rcases p409_3 (m.d 1 3) (by simp) with h415 | h415
                                        · linarith only [h1, h415, hlam]
                                        · linarith only [h403, h415, hlam]
                                      · linarith only [h414, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h1, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h1, h406, h408, hc01, hc45, hlam, hphi, ht0b, ht5b, p409_1]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h401, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      rcases p409_3 (m.d 0 3) (by simp) with h423 | h423
                                      · rcases p409_3 (m.d 1 3) (by simp) with h424 | h424
                                        · rcases p409_3 (m.d 2 3) (by simp) with h425 | h425
                                          · linarith only [h398, h425, hlam]
                                          · linarith only [h406, h425, hlam]
                                        · linarith only [h424, hlam, p409_0]
                                      · linarith only [h396, h423, hlam]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h3, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h398, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h404, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h3, h408, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p409_1, u2elo0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p409_1, u0ehi2]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      rcases p409_3 (m.d 0 3) (by simp) with h436 | h436
                                      · linarith only [h436, h5, hlam]
                                      · linarith only [h1, h436, hlam]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      rcases p409_3 (m.d 0 3) (by simp) with h439 | h439
                                      · linarith only [h439, h5, hlam]
                                      · linarith only [h3, h439, hlam]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      rcases p409_3 (m.d 0 3) (by simp) with h443 | h443
                                      · linarith only [h443, h5, hlam]
                                      · linarith only [h396, h443, hlam]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h396, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h403, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h406, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [h408, hlam, p409_0]
                                    · have p409_0 := h409c.1
                                      have p409_1 := h409c.2.1
                                      have p409_2 := h409c.2.2.1
                                      have p409_3 := h409c.2.2.2
                                      linarith only [hlam, p409_0]
                                  · linarith only [h396, h408, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4]
                                · linarith only [h397, h4, h404, h406, h407, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h1, h403, h406, h5, hc23, hc34, hlam, hphi]
                          · linarith only [h396, h403, h5, hc13, hc34, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h455 | h455
                        · linarith only [h455, h5, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h457 | h457
                          · linarith only [h399, h400, h455, h457, hlam]
                          · linarith only [h396, h457, h5, hc13, hc34, hlam, hphi]
                    · linarith only [h399, h4, hc12, hlam, hphi, u2elo0]
                  · linarith only [h3, h398, hc12, hlam, hphi, u2elo0]
                · linarith only [h396, h397, h5, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h463 | h463
                · rcases m.htr 1 2 3 (by decide) (by decide) with h464 | h464
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h465 | h465
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h466 | h466
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h467 | h467
                        · linarith only [h467, h5, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h469 | h469
                          · linarith only [h396, h465, h467, h469, hc12, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h471 | h471
                            · linarith only [h471, h5, hlam, hphi, ht01, ht12, u0ehi2, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h473 | h473
                              · linarith only [h0, h396, h465, h471, h473, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h475 | h475
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h476 | h476
                                  · rcases h3bigk with h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c | h477c
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h396, h476, hc13, hc34, hlam, hphi, p477_1]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h396, h476, hc23, hc34, hlam, hphi, p477_1]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h5, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h396, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h1, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h1, h396, h476, hc23, hc34, hlam, hphi, p477_1]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h467, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h469, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h3, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h464, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h471, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h473, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p477_1, u0ehi2]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      rcases p477_3 (m.d 0 3) (by simp) with h494 | h494
                                      · linarith only [h494, h5, hlam]
                                      · linarith only [h1, h494, hlam]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      rcases p477_3 (m.d 0 3) (by simp) with h497 | h497
                                      · linarith only [h497, h5, hlam]
                                      · linarith only [h3, h497, hlam]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h396, hc34, hlam, hphi, ht01, ht12, ht23, p477_1, u0ehi2]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht01, ht12, ht23, p477_1, u0ehi2]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      rcases p477_3 (m.d 0 3) (by simp) with h503 | h503
                                      · linarith only [h396, h503, hlam]
                                      · linarith only [h1, h503, hlam]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      rcases p477_3 (m.d 0 3) (by simp) with h506 | h506
                                      · linarith only [h396, h506, hlam]
                                      · linarith only [h3, h506, hlam]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [h476, hlam, p477_0]
                                    · have p477_0 := h477c.1
                                      have p477_1 := h477c.2.1
                                      have p477_2 := h477c.2.2.1
                                      have p477_3 := h477c.2.2.2
                                      linarith only [hlam, p477_0]
                                  · linarith only [h0, h465, h475, h476, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h512 | h512
                                  · rcases h3bigk with h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c | h513c
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h5, hc13, hc34, hlam, hphi, p513_1]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h5, hc23, hc34, hlam, hphi, p513_1]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h5, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h396, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h1, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h1, h5, hc23, hc34, hlam, hphi, p513_1]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h467, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h469, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h3, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h464, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h471, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h473, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h4, h463, h471, h475, hc23, hc34, hlam, hphi, ht01, ht12, p513_1, u0ehi2, u2elo0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      rcases p513_3 (m.d 0 3) (by simp) with h530 | h530
                                      · linarith only [h5, h530, hlam]
                                      · linarith only [h1, h530, hlam]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      rcases p513_3 (m.d 0 3) (by simp) with h533 | h533
                                      · linarith only [h5, h533, hlam]
                                      · linarith only [h3, h533, hlam]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h396, h4, h463, h471, h475, hc23, hc34, hlam, hphi, ht01, ht12, p513_1, u0ehi2, u2elo0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h4, h463, h471, h475, hc23, hc35, hlam, hphi, ht01, ht12, p513_1, u0ehi2, u2elo0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      rcases p513_3 (m.d 0 3) (by simp) with h539 | h539
                                      · linarith only [h396, h539, hlam]
                                      · linarith only [h1, h539, hlam]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      rcases p513_3 (m.d 0 3) (by simp) with h542 | h542
                                      · linarith only [h396, h542, hlam]
                                      · linarith only [h3, h542, hlam]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [h512, hlam, p513_0]
                                    · have p513_0 := h513c.1
                                      have p513_1 := h513c.2.1
                                      have p513_2 := h513c.2.2.1
                                      have p513_3 := h513c.2.2.2
                                      linarith only [hlam, p513_0]
                                  · linarith only [h4, h463, h5, h512, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                        · linarith only [h5, h548, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                          · linarith only [h396, h465, h466, h548, h550, hlam, hphi, ht01, ht12, u0ehi2, u2elo4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h552 | h552
                            · linarith only [h5, h552, hlam, hphi, ht01, ht12, u0ehi2, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h554 | h554
                              · linarith only [h396, h554, hlam, hphi, ht01, ht12, u0ehi2, u2elo2]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h556 | h556
                                · linarith only [h465, h466, h556, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                                · linarith only [h4, h463, h466, h556, hc12, hlam, hphi, u2elo0]
                    · linarith only [h4, h464, h465, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                  · linarith only [h3, h464, hc12, hlam, hphi, u2elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h561 | h561
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h562 | h562
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h563 | h563
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h564 | h564
                        · linarith only [h5, h564, hc13, hlam, hphi, ht01, u0ehi2]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h566 | h566
                          · linarith only [h396, h562, h564, h566, hc12, hlam, hphi, ht01, u0ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h568 | h568
                            · linarith only [h5, h568, hlam, hphi, ht01, ht12, u0ehi2, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h570 | h570
                              · linarith only [h0, h396, h562, h568, h570, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h572 | h572
                                · linarith only [h0, h463, h5, h562, h572, hlam, hphi, ht01, ht12, u0ehi2, u2elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h574 | h574
                                  · linarith only [h463, h5, h574, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
                                  · linarith only [h5, h574, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h577 | h577
                        · linarith only [h5, h561, h563, h577, hlam, hphi, ht01, ht12, u0ehi2, u2elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h579 | h579
                          · linarith only [h396, h562, h563, h577, h579, hlam, hphi, ht01, ht12, u0ehi2, u2elo4]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h581 | h581
                            · linarith only [h5, h581, hlam, hphi, ht01, ht12, u0ehi2, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h583 | h583
                              · linarith only [h396, h562, h563, h581, h583, hlam, hphi, ht01, ht12, u0ehi2, u2elo4]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h585 | h585
                                · linarith only [h562, h563, h585, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h587 | h587
                                  · linarith only [h463, h5, h562, h563, h581, h587, hc23, hc34, hlam, hphi, ht01, ht12, u0ehi2, u2elo4]
                                  · linarith only [h5, h562, h563, h581, h587, hc23, hc45, hlam, hphi, ht01, ht12, ht34, u0ehi2, u2elo4]
                    · linarith only [h4, h562, hc12, hlam, hphi, u2elo0]
                  · linarith only [h3, h561, hc12, hlam, hphi, u2elo0]
          · linarith only [h4, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
        · linarith only [h3, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h594 | h594
        · rcases m.htr 0 2 4 (by decide) (by decide) with h595 | h595
          · rcases m.htr 0 3 4 (by decide) (by decide) with h596 | h596
            · rcases m.htr 0 3 5 (by decide) (by decide) with h597 | h597
              · linarith only [h0, h2, h594, h597, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h599 | h599
                · linarith only [h0, h2, h594, h596, h599, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h601 | h601
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h602 | h602
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h603 | h603
                      · linarith only [h2, h603, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]
                      · linarith only [h0, h2, h594, h596, h603, hlam, hphi, ht01, ht12, u0ehi3, u2elo4]
                    · linarith only [h595, h602, hc12, hlam, hphi, u2elo0]
                  · linarith only [h594, h601, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h608 | h608
              · linarith only [h1, h2, h608, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h610 | h610
                · linarith only [h0, h2, h595, h610, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h612 | h612
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h613 | h613
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h614 | h614
                      · linarith only [h2, h614, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]
                      · linarith only [h2, h614, hlam, hphi, ht01, ht12, u0ehi0, u2elo4]
                    · linarith only [h595, h613, hc12, hlam, hphi, u2elo0]
                  · linarith only [h594, h612, hc12, hlam, hphi, u2elo0]
          · linarith only [h595, hlam, hphi, ht01, ht12, u0ehi1, u2elo3]
        · linarith only [h594, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h621 | h621
      · rcases m.htr 0 2 3 (by decide) (by decide) with h622 | h622
        · linarith only [h0, h1, h622, hlam]
        · linarith only [h622, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h625 | h625
        · linarith only [h0, h1, h625, hlam]
        · linarith only [h625, hlam, hphi, ht01, ht12, u0ehi1, u2elo2]
  · linarith only [h0, hlam, hphi, ht01, ht12, u0ehi0, u2elo1]

end R2N4
