import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_15_M_LI_L_R_x0 (m : N7Model)
    (hb1 : CMSig2_7_M_LI m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1elo := hb1.1
  have h1bigk := hb1.2.2.2
  have h5ehi := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
              · linarith only [h0, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10 | h10
                  · linarith only [h10, h3, h5, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                    · linarith only [h12, h3, h5, h7, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                      · linarith only [h14, h3, h5, h7, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                      · linarith only [h14, h3, h5, h7, h9, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                  · linarith only [h17, h3, h6, h7, h9, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
                    · linarith only [h19, h3, h6, h7, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h21 | h21
                      · linarith only [h0, h21, h4, h9, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h23 | h23
                        · linarith only [h1, h17, h23, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                          · rcases h1bigk with h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h21, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              rcases p26_3 (m.d 0 1) (by simp) with h29 | h29
                              · rcases p26_3 (m.d 1 2) (by simp) with h30 | h30
                                · linarith only [h0, h30, hlam]
                                · linarith only [h30, h5, hlam]
                              · linarith only [h29, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              rcases p26_3 (m.d 0 1) (by simp) with h34 | h34
                              · rcases p26_3 (m.d 1 2) (by simp) with h35 | h35
                                · linarith only [h0, h35, hlam]
                                · linarith only [h35, h6, hlam]
                              · linarith only [h34, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h21, h6, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h23, h7, hc13, hc35, hlam, hphi, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h3, h7, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p26_1, u1elo0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h7, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h1, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h5, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h9, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h17, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h2, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h6, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h19, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h3, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p26_1, u1elo0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u1elo0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p26_1, u1elo0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                          · rcases h1bigk with h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c | h60c
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p60_1, u1elo0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              rcases p60_3 (m.d 0 1) (by simp) with h63 | h63
                              · rcases p60_3 (m.d 1 2) (by simp) with h64 | h64
                                · linarith only [h0, h64, hlam]
                                · linarith only [h5, h64, hlam]
                              · linarith only [h63, hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              rcases p60_3 (m.d 0 1) (by simp) with h68 | h68
                              · rcases p60_3 (m.d 1 2) (by simp) with h69 | h69
                                · linarith only [h0, h69, hlam]
                                · linarith only [h6, h69, hlam]
                              · linarith only [h68, hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p60_1, u1elo0, u5ehi1]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h0, hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h0, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p60_1, u1elo0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h0, h21, h6, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p60_1, u1elo0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h7, hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h1, hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h5, hlam, p60_1]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h9, hlam, p60_1]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h17, hlam, p60_1]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h2, hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h6, hlam, p60_1]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h2, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p60_1, u1elo0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h19, hlam, p60_1]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h3, hlam, p60_0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p60_1, u1elo0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h3, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p60_1, u1elo0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p60_1, u1elo0]
                            · have p60_0 := h60c.1
                              have p60_1 := h60c.2.1
                              have p60_2 := h60c.2.2.1
                              have p60_3 := h60c.2.2.2
                              linarith only [hlam, p60_0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h94 | h94
              · linarith only [h0, h94, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h96 | h96
                · linarith only [h5, h6, h96, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                  · linarith only [h0, h5, h98, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
                    · linarith only [h100, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h102 | h102
                      · linarith only [h0, h102, h4, h96, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h104 | h104
                        · linarith only [h1, h104, h5, h98, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h106 | h106
                          · linarith only [h100, h106, h5, h6, hc23, hc34, hlam, hphi]
                          · linarith only [h102, h106, h5, h6, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
            · linarith only [h0, h109, h4, h5, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
              · linarith only [h0, h111, h4, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                  · linarith only [h1, h114, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h116 | h116
                    · linarith only [h116, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h118 | h118
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h119 | h119
                        · linarith only [h0, h114, h119, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h121 | h121
                          · linarith only [h109, h113, h116, h121, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                          · rcases h1bigk with h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c | h123c
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              rcases p123_3 (m.d 0 1) (by simp) with h125 | h125
                              · rcases p123_3 (m.d 1 2) (by simp) with h126 | h126
                                · linarith only [h126, hlam, p123_0]
                                · rcases p123_3 (m.d 1 3) (by simp) with h128 | h128
                                  · linarith only [h1, h128, hlam]
                                  · linarith only [h128, h5, hlam]
                              · linarith only [h125, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h113, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p123_1, u1elo0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              rcases p123_3 (m.d 0 1) (by simp) with h133 | h133
                              · rcases p123_3 (m.d 1 2) (by simp) with h134 | h134
                                · linarith only [h0, h134, hlam]
                                · rcases p123_3 (m.d 1 3) (by simp) with h136 | h136
                                  · linarith only [h1, h136, hlam]
                                  · linarith only [h113, h136, hlam]
                              · linarith only [h133, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p123_1, u1elo0, u5ehi1]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h0, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h5, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h109, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h111, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h1, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p123_1, u1elo0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h0, h109, h4, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p123_1, u1elo0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h114, hlam, p123_1]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h2, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p123_1, u1elo0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h113, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h116, hlam, p123_1]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h3, hlam, p123_0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p123_1, u1elo0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p123_1, u1elo0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p123_1, u1elo0]
                            · have p123_0 := h123c.1
                              have p123_1 := h123c.2.1
                              have p123_2 := h123c.2.2.1
                              have p123_3 := h123c.2.2.2
                              linarith only [hlam, p123_0]
                      · linarith only [h1, h113, h118, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                  · linarith only [h0, h162, h4, h5, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                    · linarith only [h164, h2, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h166 | h166
                      · linarith only [h0, h113, h166, h4, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h168 | h168
                        · linarith only [h0, h162, h168, h4, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h170 | h170
                          · rcases h1bigk with h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              rcases p171_3 (m.d 0 1) (by simp) with h173 | h173
                              · rcases p171_3 (m.d 1 2) (by simp) with h174 | h174
                                · linarith only [h174, hlam, p171_0]
                                · rcases p171_3 (m.d 1 3) (by simp) with h176 | h176
                                  · linarith only [h1, h176, hlam]
                                  · linarith only [h176, h5, hlam]
                              · linarith only [h173, hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              rcases p171_3 (m.d 0 1) (by simp) with h180 | h180
                              · rcases p171_3 (m.d 1 2) (by simp) with h181 | h181
                                · linarith only [h0, h181, hlam]
                                · rcases p171_3 (m.d 1 3) (by simp) with h183 | h183
                                  · linarith only [h183, hlam, p171_0]
                                  · rcases p171_3 (m.d 1 4) (by simp) with h185 | h185
                                    · linarith only [h185, h2, hlam]
                                    · linarith only [h113, h185, hlam]
                              · linarith only [h180, hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              rcases p171_3 (m.d 0 1) (by simp) with h189 | h189
                              · rcases p171_3 (m.d 1 2) (by simp) with h190 | h190
                                · linarith only [h0, h190, hlam]
                                · rcases p171_3 (m.d 1 3) (by simp) with h192 | h192
                                  · linarith only [h1, h192, hlam]
                                  · rcases p171_3 (m.d 1 4) (by simp) with h194 | h194
                                    · linarith only [h194, hlam, p171_0]
                                    · rcases p171_3 (m.d 1 5) (by simp) with h196 | h196
                                      · linarith only [h196, h3, hlam]
                                      · linarith only [h164, h196, hlam]
                              · linarith only [h189, hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p171_1, u1elo0, u5ehi1]
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
                              linarith only [h109, hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h111, hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h1, hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h113, hlam, p171_1]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h162, hlam, p171_1]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h2, hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h164, hc12, hc45, hlam, hphi, ht23, ht34, p171_1]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p171_1, u1elo0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h164, hlam, p171_1]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h3, hlam, p171_0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h3, h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u1elo0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p171_1, u1elo0]
                            · have p171_0 := h171c.1
                              have p171_1 := h171c.2.1
                              have p171_2 := h171c.2.2.1
                              have p171_3 := h171c.2.2.2
                              linarith only [hlam, p171_0]
                          · linarith only [h166, h170, h5, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
          · linarith only [h0, h222, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h224 | h224
            · rcases m.htr 1 2 5 (by decide) (by decide) with h225 | h225
              · linarith only [h0, h225, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                · rcases m.htr 1 3 5 (by decide) (by decide) with h228 | h228
                  · linarith only [h1, h228, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h230 | h230
                    · linarith only [h2, h230, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h232 | h232
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h233 | h233
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h234 | h234
                          · linarith only [h222, h224, h228, h230, h232, h234, h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases h1bigk with h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c | h236c
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h224, h232, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p236_1, u1elo0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h222, h224, h232, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p236_1, u1elo0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              rcases p236_3 (m.d 0 1) (by simp) with h240 | h240
                              · rcases p236_3 (m.d 1 2) (by simp) with h241 | h241
                                · linarith only [h0, h241, hlam]
                                · linarith only [h224, h241, hlam]
                              · linarith only [h240, hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p236_1, u1elo0, u5ehi1]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h0, hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h222, hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h222, h224, h228, h232, h233, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p236_1]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h225, hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h1, hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h228, h233, hc12, hc23, hlam, hphi, p236_1]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h224, h228, h232, h233, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p236_1]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h228, hlam, p236_1]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h2, hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h224, hlam, p236_1]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h227, hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h230, hlam, p236_1]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h3, hlam, p236_0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h224, h232, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p236_1, u1elo4]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p236_1, u1elo0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [h224, h232, h3, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p236_1, u1elo0]
                            · have p236_0 := h236c.1
                              have p236_1 := h236c.2.1
                              have p236_2 := h236c.2.2.1
                              have p236_3 := h236c.2.2.2
                              linarith only [hlam, p236_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h266 | h266
                          · linarith only [h224, h232, h266, hlam, hphi, ht01, ht0b, ht5b, u1elo1, u5ehi4]
                          · linarith only [h0, h224, h233, h266, h4, hc24, hc45, hlam, hphi]
                      · linarith only [h0, h224, h227, h228, h232, h3, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h222, h224, h227, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
              · linarith only [h0, h271, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                · rcases m.htr 1 3 5 (by decide) (by decide) with h274 | h274
                  · linarith only [h1, h274, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h276 | h276
                    · linarith only [h273, h274, h276, h3, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h279 | h279
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h280 | h280
                          · linarith only [h224, h273, h274, h276, h280, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                          · rcases h1bigk with h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c | h282c
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              rcases p282_3 (m.d 0 1) (by simp) with h284 | h284
                              · rcases p282_3 (m.d 1 2) (by simp) with h285 | h285
                                · linarith only [h285, hlam, p282_0]
                                · rcases p282_3 (m.d 1 3) (by simp) with h287 | h287
                                  · linarith only [h1, h287, hlam]
                                  · linarith only [h222, h287, hlam]
                              · linarith only [h284, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h273, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p282_1, u1elo0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              rcases p282_3 (m.d 0 1) (by simp) with h292 | h292
                              · rcases p282_3 (m.d 1 2) (by simp) with h293 | h293
                                · linarith only [h0, h293, hlam]
                                · rcases p282_3 (m.d 1 3) (by simp) with h295 | h295
                                  · linarith only [h1, h295, hlam]
                                  · linarith only [h273, h295, hlam]
                              · linarith only [h292, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p282_1, u1elo0, u5ehi1]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h0, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h222, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h224, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h271, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h1, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p282_1, u1elo0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h1, h224, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p282_1, u1elo0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h274, hlam, p282_1]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h2, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p282_1, u1elo0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h273, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h276, hlam, p282_1]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h3, hlam, p282_0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p282_1, u1elo0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p282_1, u1elo0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [h224, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p282_1, u1elo0]
                            · have p282_0 := h282c.1
                              have p282_1 := h282c.2.1
                              have p282_2 := h282c.2.2.1
                              have p282_3 := h282c.2.2.2
                              linarith only [hlam, p282_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h320 | h320
                          · linarith only [h273, h320, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                          · rcases h1bigk with h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c | h322c
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              rcases p322_3 (m.d 0 1) (by simp) with h324 | h324
                              · rcases p322_3 (m.d 1 2) (by simp) with h325 | h325
                                · linarith only [h325, hlam, p322_0]
                                · rcases p322_3 (m.d 1 3) (by simp) with h327 | h327
                                  · linarith only [h1, h327, hlam]
                                  · linarith only [h222, h327, hlam]
                              · linarith only [h324, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h273, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p322_1, u1elo0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              rcases p322_3 (m.d 0 1) (by simp) with h332 | h332
                              · rcases p322_3 (m.d 1 2) (by simp) with h333 | h333
                                · linarith only [h0, h333, hlam]
                                · rcases p322_3 (m.d 1 3) (by simp) with h335 | h335
                                  · linarith only [h1, h335, hlam]
                                  · linarith only [h273, h335, hlam]
                              · linarith only [h332, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p322_1, u1elo0, u5ehi1]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h0, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h222, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h224, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h271, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h1, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p322_1, u1elo0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h1, h224, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p322_1, u1elo0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h274, hlam, p322_1]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h2, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p322_1, u1elo0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h273, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h276, hlam, p322_1]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h3, hlam, p322_0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p322_1, u1elo0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h3, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p322_1, u1elo0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [h224, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p322_1, u1elo0]
                            · have p322_0 := h322c.1
                              have p322_1 := h322c.2.1
                              have p322_2 := h322c.2.2.1
                              have p322_3 := h322c.2.2.2
                              linarith only [hlam, p322_0]
                      · linarith only [h273, h278, h4, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                  · linarith only [h2, h273, h361, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h363 | h363
                    · linarith only [h2, h363, hlam, hphi, ht01, ht0b, ht5b, u1elo0, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h365 | h365
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h366 | h366
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h367 | h367
                          · linarith only [h222, h273, h363, h365, h367, hc12, hc23, hlam, hphi]
                          · rcases h1bigk with h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c | h369c
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              rcases p369_3 (m.d 0 1) (by simp) with h371 | h371
                              · rcases p369_3 (m.d 1 2) (by simp) with h372 | h372
                                · linarith only [h372, hlam, p369_0]
                                · rcases p369_3 (m.d 1 3) (by simp) with h374 | h374
                                  · linarith only [h1, h374, hlam]
                                  · linarith only [h222, h374, hlam]
                              · linarith only [h371, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              rcases p369_3 (m.d 0 1) (by simp) with h378 | h378
                              · rcases p369_3 (m.d 1 2) (by simp) with h379 | h379
                                · linarith only [h0, h379, hlam]
                                · rcases p369_3 (m.d 1 3) (by simp) with h381 | h381
                                  · linarith only [h381, hlam, p369_0]
                                  · rcases p369_3 (m.d 1 4) (by simp) with h383 | h383
                                    · linarith only [h2, h383, hlam]
                                    · linarith only [h273, h383, hlam]
                              · linarith only [h378, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              rcases p369_3 (m.d 0 1) (by simp) with h387 | h387
                              · rcases p369_3 (m.d 1 2) (by simp) with h388 | h388
                                · linarith only [h0, h388, hlam]
                                · rcases p369_3 (m.d 1 3) (by simp) with h390 | h390
                                  · linarith only [h1, h390, hlam]
                                  · rcases p369_3 (m.d 1 4) (by simp) with h392 | h392
                                    · linarith only [h392, hlam, p369_0]
                                    · rcases p369_3 (m.d 1 5) (by simp) with h394 | h394
                                      · linarith only [h3, h394, hlam]
                                      · linarith only [h363, h394, hlam]
                              · linarith only [h387, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p369_1, u1elo0, u5ehi1]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h0, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h222, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h224, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h271, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h1, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p369_1, u1elo0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h273, hlam, p369_1]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h361, hlam, p369_1]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h2, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p369_1, u1elo0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p369_1, u1elo0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h363, hlam, p369_1]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h3, hlam, p369_0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p369_1, u1elo0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h222, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p369_1, u1elo0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p369_1, u1elo0]
                            · have p369_0 := h369c.1
                              have p369_1 := h369c.2.1
                              have p369_2 := h369c.2.2.1
                              have p369_3 := h369c.2.2.2
                              linarith only [hlam, p369_0]
                        · linarith only [h222, h273, h365, h366, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h420 | h420
                        · linarith only [h222, h361, h365, h420, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h422 | h422
                          · rcases h1bigk with h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c | h423c
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              rcases p423_3 (m.d 0 1) (by simp) with h425 | h425
                              · rcases p423_3 (m.d 1 2) (by simp) with h426 | h426
                                · linarith only [h426, hlam, p423_0]
                                · rcases p423_3 (m.d 1 3) (by simp) with h428 | h428
                                  · linarith only [h1, h428, hlam]
                                  · linarith only [h222, h428, hlam]
                              · linarith only [h425, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              rcases p423_3 (m.d 0 1) (by simp) with h432 | h432
                              · rcases p423_3 (m.d 1 2) (by simp) with h433 | h433
                                · linarith only [h0, h433, hlam]
                                · rcases p423_3 (m.d 1 3) (by simp) with h435 | h435
                                  · linarith only [h435, hlam, p423_0]
                                  · rcases p423_3 (m.d 1 4) (by simp) with h437 | h437
                                    · linarith only [h2, h437, hlam]
                                    · linarith only [h273, h437, hlam]
                              · linarith only [h432, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              rcases p423_3 (m.d 0 1) (by simp) with h441 | h441
                              · rcases p423_3 (m.d 1 2) (by simp) with h442 | h442
                                · linarith only [h0, h442, hlam]
                                · rcases p423_3 (m.d 1 3) (by simp) with h444 | h444
                                  · linarith only [h1, h444, hlam]
                                  · rcases p423_3 (m.d 1 4) (by simp) with h446 | h446
                                    · linarith only [h446, hlam, p423_0]
                                    · rcases p423_3 (m.d 1 5) (by simp) with h448 | h448
                                      · linarith only [h3, h448, hlam]
                                      · linarith only [h363, h448, hlam]
                              · linarith only [h441, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p423_1, u1elo0, u5ehi1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h0, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h222, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h224, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h271, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h1, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h1, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p423_1, u1elo0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h273, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h361, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h2, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h2, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p423_1, u1elo0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h2, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p423_1, u1elo0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h363, hlam, p423_1]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h3, hlam, p423_0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p423_1, u1elo0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h222, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p423_1, u1elo0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [h3, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p423_1, u1elo0]
                            · have p423_0 := h423c.1
                              have p423_1 := h423c.2.1
                              have p423_2 := h423c.2.2.1
                              have p423_3 := h423c.2.2.2
                              linarith only [hlam, p423_0]
                          · linarith only [h0, h365, h4, h422, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h474 | h474
        · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
          · linarith only [h0, h3, h475, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo4]
          · linarith only [h0, h3, h474, h475, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h478 | h478
          · linarith only [h0, h3, h474, h478, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h480 | h480
            · linarith only [h0, h3, h480, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h482 | h482
              · linarith only [h1, h3, h478, h482, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h484 | h484
                · linarith only [h1, h3, h484, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h486 | h486
                  · linarith only [h2, h3, h484, h486, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h488 | h488
                    · linarith only [h2, h3, h488, hlam, hphi, ht01, ht0b, ht5b, u1elo4, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h490 | h490
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h491 | h491
                        · linarith only [h2, h3, h478, h484, h486, h491, hc12, hc23, hlam, hphi]
                        · linarith only [h478, h484, h490, h491, hc12, hc35, hlam, hphi, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h494 | h494
                        · linarith only [h478, h486, h490, h494, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h496 | h496
                          · linarith only [h2, h3, h478, h484, h488, h496, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h474, h490, h496, hc02, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h499 | h499
      · linarith only [h2, h499, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h501 | h501
        · rcases m.htr 1 2 3 (by decide) (by decide) with h502 | h502
          · linarith only [h0, h2, h502, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo3]
          · linarith only [h0, h2, h501, h502, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h505 | h505
          · linarith only [h0, h2, h501, h505, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h507 | h507
            · linarith only [h0, h2, h507, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h509 | h509
              · linarith only [h1, h2, h505, h509, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h511 | h511
                · linarith only [h1, h2, h511, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h513 | h513
                  · linarith only [h1, h2, h513, hlam, hphi, ht01, ht0b, ht5b, u1elo3, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h515 | h515
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h516 | h516
                      · linarith only [h1, h499, h505, h511, h515, h516, hc12, hc23, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h518 | h518
                        · linarith only [h1, h499, h505, h513, h516, h518, hc12, hc34, hlam, hphi, ht23]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h520 | h520
                          · rcases h1bigk with h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h499, h515, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p521_1, u1elo3]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h499, h515, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p521_1, u1elo3]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h2, hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h499, hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h0, hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h505, hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h507, hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h509, hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h1, hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h1, h499, h515, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p521_1, u1elo3]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h511, hlam, p521_1]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h513, hlam, p521_1]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [hc01, hlam, hphi, p521_1, u1elo3]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              rcases p521_3 (m.d 0 1) (by simp) with h538 | h538
                              · linarith only [h2, h538, hlam]
                              · linarith only [h0, h538, hlam]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              rcases p521_3 (m.d 0 1) (by simp) with h541 | h541
                              · linarith only [h2, h541, hlam]
                              · linarith only [h1, h541, hlam]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h499, hlam, hphi, ht01, ht0b, ht5b, p521_1, u1elo3, u5ehi0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h1, h505, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p521_1, u1elo4]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              rcases p521_3 (m.d 0 1) (by simp) with h547 | h547
                              · linarith only [h499, h547, hlam]
                              · linarith only [h0, h547, hlam]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              rcases p521_3 (m.d 0 1) (by simp) with h550 | h550
                              · linarith only [h499, h550, hlam]
                              · linarith only [h1, h550, hlam]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [h515, hlam, p521_0]
                            · have p521_0 := h521c.1
                              have p521_1 := h521c.2.1
                              have p521_2 := h521c.2.2.1
                              have p521_3 := h521c.2.2.2
                              linarith only [hlam, p521_0]
                          · linarith only [h505, h511, h515, h520, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3]
                    · linarith only [h1, h2, h505, h515, hc12, hc45, hlam, hphi, ht23, ht34]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h557 | h557
    · rcases m.htr 0 1 5 (by decide) (by decide) with h558 | h558
      · linarith only [h1, h558, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h560 | h560
        · linarith only [h0, h1, h560, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
          · linarith only [h0, h1, h560, h562, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h564 | h564
            · linarith only [h0, h1, h564, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h566 | h566
              · linarith only [h1, h557, h564, h566, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h568 | h568
                · rcases m.htr 1 3 5 (by decide) (by decide) with h569 | h569
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h570 | h570
                    · linarith only [h557, h558, h569, h570, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h572 | h572
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h573 | h573
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h574 | h574
                          · linarith only [h557, h558, h568, h570, h574, hlam]
                          · rcases h1bigk with h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c | h576c
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h558, h569, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p576_1, u1elo2]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h1, hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h558, h569, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p576_1, u1elo2]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h558, hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h0, hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h562, hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h564, hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h566, hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [hc01, hlam, hphi, p576_1, u1elo2]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              rcases p576_3 (m.d 0 1) (by simp) with h588 | h588
                              · linarith only [h1, h588, hlam]
                              · linarith only [h0, h588, hlam]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              rcases p576_3 (m.d 0 1) (by simp) with h592 | h592
                              · linarith only [h1, h592, hlam]
                              · linarith only [h557, h592, hlam]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [hlam, hphi, ht01, ht0b, ht5b, p576_1, u1elo2, u5ehi1]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h557, hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h557, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p576_1, u1elo0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h568, hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h570, hlam, p576_1]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [hc01, hlam, hphi, p576_1, u1elo4]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              rcases p576_3 (m.d 0 1) (by simp) with h602 | h602
                              · linarith only [h558, h602, hlam]
                              · linarith only [h0, h602, hlam]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [h569, hlam, p576_0]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              rcases p576_3 (m.d 0 1) (by simp) with h606 | h606
                              · linarith only [h558, h606, hlam]
                              · linarith only [h557, h606, hlam]
                            · have p576_0 := h576c.1
                              have p576_1 := h576c.2.1
                              have p576_2 := h576c.2.2.1
                              have p576_3 := h576c.2.2.2
                              linarith only [hlam, p576_0]
                        · linarith only [h562, h569, h573, hlam]
                      · linarith only [h1, h557, h562, h564, h572, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h557, h564, h569, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h1, h557, h564, h568, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h614 | h614
      · linarith only [h1, h614, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi1]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h616 | h616
        · linarith only [h0, h1, h616, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h618 | h618
          · linarith only [h0, h1, h616, h618, hc02, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h620 | h620
            · linarith only [h0, h1, h620, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h622 | h622
              · linarith only [h0, h1, h622, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h624 | h624
                · rcases m.htr 1 3 5 (by decide) (by decide) with h625 | h625
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h626 | h626
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h627 | h627
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h628 | h628
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h629 | h629
                          · linarith only [h624, h629, hlam, hphi, ht01, ht0b, ht5b, u1elo2, u5ehi4]
                          · rcases h1bigk with h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h614, h624, h626, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p631_1, u1elo2]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h1, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h557, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h614, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h618, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h620, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h622, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hc01, hlam, hphi, p631_1, u1elo2]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              rcases p631_3 (m.d 0 1) (by simp) with h643 | h643
                              · linarith only [h1, h643, hlam]
                              · linarith only [h0, h643, hlam]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h626, hlam, hphi, ht01, ht0b, ht5b, p631_1, u1elo2, u5ehi1]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, h614, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p631_1, u1elo2]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p631_1, u1elo3]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              rcases p631_3 (m.d 0 1) (by simp) with h650 | h650
                              · linarith only [h557, h650, hlam]
                              · linarith only [h0, h650, hlam]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h624, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, h614, h624, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p631_1, u1elo2]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p631_1, u1elo4]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              rcases p631_3 (m.d 0 1) (by simp) with h657 | h657
                              · linarith only [h614, h657, hlam]
                              · linarith only [h0, h657, hlam]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h625, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [h626, hlam, p631_0]
                            · have p631_0 := h631c.1
                              have p631_1 := h631c.2.1
                              have p631_2 := h631c.2.2.1
                              have p631_3 := h631c.2.2.2
                              linarith only [hlam, p631_0]
                        · linarith only [h0, h1, h618, h628, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h618, h627, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h557, h626, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h0, h557, h624, h625, hc12, hc35, hlam, hphi, ht23]
                · linarith only [h0, h1, h624, hc12, hc34, hlam, hphi, ht23]

end R2N4
