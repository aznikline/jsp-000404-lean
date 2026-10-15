import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_H_L_L_I_L_I (m : N7Model)
    (hb2 : CMSig2_7_H_L m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · linarith only [h13, h3, h5, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · linarith only [h12, h3, h5, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h17 | h17
                          · linarith only [h10, h11, h17, hlam]
                          · linarith only [h17, h3, h5, h6, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                      · linarith only [h10, h3, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h9, hc12, hlam, hphi, u2elo4]
                  · linarith only [h7, h8, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h7, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h26 | h26
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h27 | h27
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h29 | h29
                          · linarith only [h25, h29, h6, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h31 | h31
                            · linarith only [h3, h31, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · linarith only [h1, h27, h3, h31, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h0, h25, h34, h5, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h36 | h36
                            · linarith only [h3, h36, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · linarith only [h27, h28, h36, hc23, hc35, hlam, hphi]
                      · linarith only [h27, h3, h5, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h26, hc12, hlam, hphi, u2elo4]
                  · linarith only [h24, h25, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h24, hc12, hlam, hphi, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h43 | h43
              · rcases m.htr 1 2 3 (by decide) (by decide) with h44 | h44
                · rcases m.htr 1 2 4 (by decide) (by decide) with h45 | h45
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h46 | h46
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h47 | h47
                      · linarith only [h1, h47, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h49 | h49
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h50 | h50
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h51 | h51
                            · linarith only [h1, h44, h49, h5, h51, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h53 | h53
                              · linarith only [h0, h45, h51, h53, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h1, h49, h5, h53, hc23, hc34, hlam, hphi]
                          · linarith only [h4, h43, h47, h49, h50, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h57 | h57
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h58 | h58
                            · linarith only [h5, h58, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h60 | h60
                              · linarith only [h0, h45, h49, h58, h60, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h62 | h62
                                · linarith only [h0, h45, h62, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · linarith only [h0, h45, h57, h62, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                            · linarith only [h43, h44, h47, h5, h57, h65, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                              · linarith only [h3, h49, h67, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h69 | h69
                                · linarith only [h44, h47, h57, h69, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
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
                                      linarith only [h3, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h5, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h44, h47, h5, h57, h71, hc23, hc34, hlam, hphi, p72_1]
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
                                      linarith only [h43, h47, h57, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p72_1]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h47, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h49, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h3, hlam, p72_1]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h44, hlam, p72_1]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h65, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h67, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      rcases p72_3 (m.d 0 3) (by simp) with h88 | h88
                                      · linarith only [h88, hlam, p72_0]
                                      · rcases p72_3 (m.d 1 3) (by simp) with h90 | h90
                                        · linarith only [h47, h90, hlam]
                                        · rcases p72_3 (m.d 2 3) (by simp) with h92 | h92
                                          · linarith only [h65, h92, hlam]
                                          · rcases p72_3 (m.d 3 4) (by simp) with h94 | h94
                                            · rcases p72_3 (m.d 3 5) (by simp) with h95 | h95
                                              · linarith only [h71, h95, hlam]
                                              · linarith only [h47, h57, h71, h95, hc13, hc34, hlam, hphi, p72_1]
                                            · linarith only [h94, hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      rcases p72_3 (m.d 0 3) (by simp) with h99 | h99
                                      · linarith only [h5, h99, hlam]
                                      · linarith only [h1, h99, hlam]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      rcases p72_3 (m.d 0 3) (by simp) with h102 | h102
                                      · linarith only [h102, h5, hlam]
                                      · linarith only [h102, h3, hlam]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [hlam, p72_0]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h44, h47, h57, h71, hc23, hc34, hlam, hphi, p72_1]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      rcases p72_3 (m.d 0 3) (by simp) with h107 | h107
                                      · linarith only [h107, hlam, p72_0]
                                      · rcases p72_3 (m.d 1 3) (by simp) with h109 | h109
                                        · linarith only [h109, h49, hlam]
                                        · rcases p72_3 (m.d 2 3) (by simp) with h111 | h111
                                          · linarith only [h111, h67, hlam]
                                          · rcases p72_3 (m.d 3 4) (by simp) with h113 | h113
                                            · rcases p72_3 (m.d 3 5) (by simp) with h114 | h114
                                              · rcases h5bigk with h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c | h115c
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [hlam, p115_0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h4, h44, h47, h57, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p115_1, u2elo0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h4, h65, h69, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p115_1, u2elo0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h1, h4, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p115_1, p72_1, u2elo0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h4, h44, h47, h57, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p115_1, u2elo0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h2, hlam, p115_0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [hlam, p115_0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h2, h4, h65, h69, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p115_1, u2elo0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h49, hlam, p115_0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h57, hlam, p115_0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h4, hlam, p115_1]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h46, hlam, p115_1]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [hlam, p115_0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h67, hlam, p115_1]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h69, hlam, p115_0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h43, h44, h47, h57, hc23, hc35, hlam, hphi, p115_1]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  rcases p115_3 (m.d 0 5) (by simp) with h132 | h132
                                                  · linarith only [h132, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p115_1, u2elo0]
                                                  · linarith only [h132, h2, hlam]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  rcases p115_3 (m.d 0 5) (by simp) with h135 | h135
                                                  · linarith only [h135, h4, h65, h69, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p115_1, u2elo0]
                                                  · linarith only [h135, h4, hlam]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [hlam, p115_0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h44, h47, h57, hc23, hc35, hlam, hphi, p115_1]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h43, hlam, p115_1]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h43, h46, h5, h65, h69, hc23, hc34, hlam, hphi, p115_1]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h4, h43, h65, h69, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p115_1, u2elo0]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [h71, hlam, p115_1]
                                                · have p115_0 := h115c.1
                                                  have p115_1 := h115c.2.1
                                                  have p115_2 := h115c.2.2.1
                                                  have p115_3 := h115c.2.2.2
                                                  linarith only [hlam, p115_0]
                                              · linarith only [h114, hlam, p72_0]
                                            · linarith only [h113, h5, hlam]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      rcases p72_3 (m.d 0 3) (by simp) with h147 | h147
                                      · linarith only [h147, h3, h44, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                      · linarith only [h1, h147, hlam]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      rcases p72_3 (m.d 0 3) (by simp) with h150 | h150
                                      · linarith only [h150, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p72_1, u2elo0]
                                      · linarith only [h150, h3, hlam]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [h71, hlam, p72_1]
                                    · have p72_0 := h72c.1
                                      have p72_1 := h72c.2.1
                                      have p72_2 := h72c.2.2.1
                                      have p72_3 := h72c.2.2.2
                                      linarith only [hlam, p72_0]
                                  · linarith only [h4, h43, h5, h71, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                    · linarith only [h46, hc12, hlam, hphi, u2elo4]
                  · linarith only [h44, h45, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h44, hc12, hlam, hphi, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h159 | h159
                · rcases m.htr 1 2 4 (by decide) (by decide) with h160 | h160
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h161 | h161
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h162 | h162
                      · linarith only [h1, h162, h5, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h164 | h164
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h165 | h165
                          · linarith only [h1, h160, h164, h165, h43, h5, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h162, h164, h165, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h168 | h168
                          · linarith only [h0, h160, h168, h43, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h170 | h170
                            · linarith only [h162, h170, h3, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h172 | h172
                              · linarith only [h0, h160, h164, h170, h172, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h174 | h174
                                · linarith only [h0, h160, h174, h43, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h176 | h176
                                  · rcases h3bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h159, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u2elo0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u2elo0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h5, hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h176, h43, h5, hlam, p177_1]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h1, hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h1, h176, h43, h5, hc23, hc34, hlam, hphi, p177_1]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h162, hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h164, hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h3, hlam, p177_1]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h159, hlam, p177_1]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h170, hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h172, hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      rcases p177_3 (m.d 0 3) (by simp) with h193 | h193
                                      · linarith only [h193, hlam, p177_0]
                                      · rcases p177_3 (m.d 1 3) (by simp) with h195 | h195
                                        · linarith only [h162, h195, hlam]
                                        · rcases p177_3 (m.d 2 3) (by simp) with h197 | h197
                                          · linarith only [h170, h197, hlam]
                                          · rcases p177_3 (m.d 3 4) (by simp) with h199 | h199
                                            · rcases p177_3 (m.d 3 5) (by simp) with h200 | h200
                                              · linarith only [h176, h200, hlam]
                                              · linarith only [h176, h200, h43, h5, hlam]
                                            · linarith only [h199, hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      rcases p177_3 (m.d 0 3) (by simp) with h204 | h204
                                      · linarith only [h204, h5, hlam]
                                      · linarith only [h1, h204, hlam]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      rcases p177_3 (m.d 0 3) (by simp) with h207 | h207
                                      · linarith only [h207, h5, hlam]
                                      · linarith only [h207, h3, hlam]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [hlam, p177_0]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h176, h43, h5, hc03, hc34, hlam, hphi, p177_1]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      rcases p177_3 (m.d 0 3) (by simp) with h212 | h212
                                      · linarith only [h212, hlam, p177_0]
                                      · rcases p177_3 (m.d 1 3) (by simp) with h214 | h214
                                        · linarith only [h164, h214, hlam]
                                        · rcases p177_3 (m.d 2 3) (by simp) with h216 | h216
                                          · linarith only [h172, h216, hlam]
                                          · rcases p177_3 (m.d 3 4) (by simp) with h218 | h218
                                            · rcases p177_3 (m.d 3 5) (by simp) with h219 | h219
                                              · rcases h5bigk with h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c | h220c
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p220_1, u2elo0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p220_1, u2elo0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h1, h159, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, p220_1, u2elo0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h43, hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h2, hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h170, h174, h2, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p220_1, u2elo0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h164, hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h168, hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h4, hlam, p220_1]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h161, hlam, p220_1]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h172, hlam, p220_1]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h174, hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  rcases p220_3 (m.d 0 5) (by simp) with h236 | h236
                                                  · linarith only [h236, hlam, p220_0]
                                                  · rcases p220_3 (m.d 1 5) (by simp) with h238 | h238
                                                    · linarith only [h164, h238, hlam]
                                                    · rcases p220_3 (m.d 2 5) (by simp) with h240 | h240
                                                      · linarith only [h172, h240, hlam]
                                                      · rcases p220_3 (m.d 3 5) (by simp) with h242 | h242
                                                        · rcases p220_3 (m.d 4 5) (by simp) with h243 | h243
                                                          · linarith only [h176, h243, hlam]
                                                          · linarith only [h243, h43, hlam]
                                                        · linarith only [h242, hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  rcases p220_3 (m.d 0 5) (by simp) with h247 | h247
                                                  · linarith only [h247, h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p220_1, u2elo0]
                                                  · linarith only [h2, h247, hlam]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  rcases p220_3 (m.d 0 5) (by simp) with h250 | h250
                                                  · linarith only [h170, h174, h250, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p220_1, u2elo0]
                                                  · linarith only [h250, h4, hlam]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [hlam, p220_0]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h1, h159, h43, h5, hc23, hc35, hlam, hphi, p220_1]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h161, h170, h174, h176, h2, hc23, hc34, hlam, hphi, p220_1]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h161, h170, h174, h176, hc23, hc34, hlam, hphi, p220_1]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h170, h174, h176, hc23, hc34, hlam, hphi, p220_1]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [h176, hlam, p220_1]
                                                · have p220_0 := h220c.1
                                                  have p220_1 := h220c.2.1
                                                  have p220_2 := h220c.2.2.1
                                                  have p220_3 := h220c.2.2.2
                                                  linarith only [hlam, p220_0]
                                              · linarith only [h219, hlam, p177_0]
                                            · linarith only [h218, h5, hlam]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      rcases p177_3 (m.d 0 3) (by simp) with h262 | h262
                                      · linarith only [h159, h262, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p177_1, u2elo0]
                                      · linarith only [h1, h262, hlam]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      rcases p177_3 (m.d 0 3) (by simp) with h265 | h265
                                      · linarith only [h159, h164, h176, h265, h43, h5, hc23, hc34, hlam, hphi]
                                      · linarith only [h265, h3, hlam]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [h176, hlam, p177_1]
                                    · have p177_0 := h177c.1
                                      have p177_1 := h177c.2.1
                                      have p177_2 := h177c.2.2.1
                                      have p177_3 := h177c.2.2.2
                                      linarith only [hlam, p177_0]
                                  · rcases h3bigk with h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c | h270c
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h159, h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p270_1, u2elo0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p270_1, u2elo0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h5, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h176, h5, hlam, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h1, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h1, h176, h5, hc23, hc45, hlam, hphi, ht34, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h162, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h164, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h3, hlam, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h159, hlam, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h170, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h172, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h176, hc03, hc45, hlam, hphi, ht34, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h176, hc13, hc45, hlam, hphi, ht34, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h176, hc23, hc45, hlam, hphi, ht34, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h176, hlam, p270_0]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      rcases p270_3 (m.d 0 3) (by simp) with h291 | h291
                                      · linarith only [h291, hlam, p270_0]
                                      · rcases p270_3 (m.d 1 3) (by simp) with h293 | h293
                                        · linarith only [h164, h293, hlam]
                                        · rcases p270_3 (m.d 2 3) (by simp) with h295 | h295
                                          · linarith only [h172, h295, hlam]
                                          · rcases p270_3 (m.d 3 4) (by simp) with h297 | h297
                                            · linarith only [h176, h297, hlam]
                                            · linarith only [h297, h5, hlam]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      rcases p270_3 (m.d 0 3) (by simp) with h300 | h300
                                      · linarith only [h159, h3, h300, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p270_1, u2elo0]
                                      · linarith only [h1, h300, hlam]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      rcases p270_3 (m.d 0 3) (by simp) with h303 | h303
                                      · linarith only [h159, h164, h176, h303, h5, hc23, hc45, hlam, hphi, ht34]
                                      · linarith only [h3, h303, hlam]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [h5, hc03, hc35, hlam, hphi, p270_1]
                                    · have p270_0 := h270c.1
                                      have p270_1 := h270c.2.1
                                      have p270_2 := h270c.2.2.1
                                      have p270_3 := h270c.2.2.2
                                      linarith only [hlam, p270_0]
                    · linarith only [h161, hc12, hlam, hphi, u2elo4]
                  · linarith only [h159, h160, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h159, hc12, hlam, hphi, u2elo2]
          · linarith only [h4, hc02, hlam, hphi, u2elo4]
        · linarith only [h0, h3, hc12, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
        · rcases m.htr 0 2 5 (by decide) (by decide) with h314 | h314
          · linarith only [h0, h2, h314, hc12, hlam, hphi, u2elo0]
          · linarith only [h314, hc02, hlam, hphi, u2elo4]
        · linarith only [h0, h313, hc12, hlam, hphi, u2elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h318 | h318
      · rcases m.htr 0 2 3 (by decide) (by decide) with h319 | h319
        · linarith only [h0, h1, h319, hc12, hlam, hphi, u2elo0]
        · linarith only [h319, hc02, hlam, hphi, u2elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h322 | h322
        · linarith only [h0, h1, h322, hc12, hlam, hphi, u2elo0]
        · linarith only [h322, hc02, hlam, hphi, u2elo2]
  · linarith only [h0, hc01, hlam, hphi, ht12, u2elo1]

theorem r1l7_22_13_15_M_LI_L_0_L_R (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc24 := m.hcor 2 4 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3elo := hb3.1
  have h5ehi := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h3, h7, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h5, h6, h7, h9, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                  · rcases h2bigk with h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c | h11c
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h5, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      rcases p11_3 (m.d 0 2) (by simp) with h15 | h15
                      · rcases p11_3 (m.d 1 2) (by simp) with h16 | h16
                        · linarith only [h0, h16, hlam]
                        · linarith only [h16, h4, hlam]
                      · linarith only [h15, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, hlam, p11_1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo1]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      rcases p11_3 (m.d 0 2) (by simp) with h24 | h24
                      · rcases p11_3 (m.d 1 2) (by simp) with h25 | h25
                        · rcases p11_3 (m.d 2 3) (by simp) with h26 | h26
                          · linarith only [h26, h3, hlam]
                          · linarith only [h26, h6, hlam]
                        · linarith only [h25, hlam, p11_0]
                      · linarith only [h1, h24, hlam]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h6, h7, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hc02, hlam, hphi, p11_1, u2elo2]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h3, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h3, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h7, hlam, p11_1]
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
                      linarith only [h6, hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h9, hlam, p11_0]
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
                      linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [h0, h5, h6, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11_1, u2elo0]
                    · have p11_0 := h11c.1
                      have p11_1 := h11c.2.1
                      have p11_2 := h11c.2.2.1
                      have p11_3 := h11c.2.2.2
                      linarith only [hlam, p11_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h47 | h47
                · linarith only [h47, h6, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
                  · linarith only [h0, h4, h49, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                  · rcases h2bigk with h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [hc12, hlam, hphi, p51_1, u2elo0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      rcases p51_3 (m.d 0 2) (by simp) with h54 | h54
                      · rcases p51_3 (m.d 1 2) (by simp) with h55 | h55
                        · linarith only [h0, h55, hlam]
                        · linarith only [h3, h55, hlam]
                      · linarith only [h54, hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      rcases p51_3 (m.d 0 2) (by simp) with h59 | h59
                      · rcases p51_3 (m.d 1 2) (by simp) with h60 | h60
                        · linarith only [h0, h60, hlam]
                        · linarith only [h4, h60, hlam]
                      · linarith only [h59, hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p51_1, u2elo0, u5ehi2]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h0, hlam, p51_1]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      rcases p51_3 (m.d 0 2) (by simp) with h67 | h67
                      · rcases p51_3 (m.d 1 2) (by simp) with h68 | h68
                        · rcases p51_3 (m.d 2 3) (by simp) with h69 | h69
                          · linarith only [h69, hlam, p51_0]
                          · rcases p51_3 (m.d 2 4) (by simp) with h71 | h71
                            · linarith only [h4, h71, hlam]
                            · linarith only [h6, h71, hlam]
                        · linarith only [h68, hlam, p51_0]
                      · linarith only [h67, hc02, hlam, hphi, p51_1, u2elo1]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      rcases p51_3 (m.d 0 2) (by simp) with h76 | h76
                      · rcases p51_3 (m.d 1 2) (by simp) with h77 | h77
                        · rcases p51_3 (m.d 2 3) (by simp) with h78 | h78
                          · linarith only [h3, h78, hlam]
                          · rcases p51_3 (m.d 2 4) (by simp) with h80 | h80
                            · linarith only [h80, hlam, p51_0]
                            · rcases p51_3 (m.d 2 5) (by simp) with h82 | h82
                              · linarith only [h5, h82, hlam]
                              · linarith only [h49, h82, hlam]
                        · linarith only [h77, hlam, p51_0]
                      · linarith only [h1, h76, hlam]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h0, hlam, hphi, ht01, ht0b, ht12, ht5b, p51_1, u2elo0, u5ehi2]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [hc02, hlam, hphi, p51_1, u2elo2]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h3, hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h6, hlam, p51_1]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h47, hlam, p51_1]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h1, hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h4, hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h49, hc23, hc45, hlam, hphi, ht34, p51_1]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h49, hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h2, hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h5, hlam, p51_0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h2, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p51_1, u2elo0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [h0, h5, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p51_1, u2elo0]
                    · have p51_0 := h51c.1
                      have p51_1 := h51c.2.1
                      have p51_2 := h51c.2.2.1
                      have p51_3 := h51c.2.2.2
                      linarith only [hlam, p51_0]
            · linarith only [h2, h5, hc12, hlam, hphi, u2elo0]
          · linarith only [h1, h3, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h105 | h105
          · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
            · linarith only [h106, h3, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2, u5ehi2]
            · linarith only [h106, h2, hc12, hlam, hphi, u2elo0]
          · linarith only [h1, h105, hc12, hlam, hphi, u2elo0]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h110 | h110
        · rcases m.htr 1 2 4 (by decide) (by decide) with h111 | h111
          · rcases m.htr 1 2 5 (by decide) (by decide) with h112 | h112
            · linarith only [h0, h112, h2, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h114 | h114
              · linarith only [h0, h110, h114, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h116 | h116
                · linarith only [h0, h111, h114, h116, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi3]
                · linarith only [h0, h111, h114, h116, h2, hc23, hlam, hphi, u3elo4]
          · linarith only [h1, h111, h2, hc12, hlam, hphi, u2elo4]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h120 | h120
          · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
            · linarith only [h110, h121, h2, hc02, hlam, hphi, u2elo2]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h123 | h123
              · rcases m.htr 2 3 5 (by decide) (by decide) with h124 | h124
                · rcases m.htr 2 4 5 (by decide) (by decide) with h125 | h125
                  · linarith only [h0, h120, h125, h2, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4, u5ehi4]
                  · rcases h2bigk with h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c | h127c
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h120, h123, h124, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p127_1, u3elo2]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h124, h2, hlam, p127_1]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h123, h124, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p127_1, u3elo2]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h2, hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h0, hlam, p127_1]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h110, hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h0, h123, h124, h2, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p127_1, u3elo2]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h121, hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [hc02, hlam, hphi, ht23, p127_1, u3elo2]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [hc12, hlam, hphi, ht23, p127_1, u3elo2]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      rcases p127_3 (m.d 0 2) (by simp) with h141 | h141
                      · linarith only [h124, h141, h2, hlam]
                      · linarith only [h1, h141, hlam]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p127_1, u3elo2, u5ehi2]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h1, hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h120, hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h123, hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h125, hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [hc02, hlam, hphi, p127_1, u2elo4]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h120, h123, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p127_1, u2elo4]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [h124, hlam, p127_0]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      rcases p127_3 (m.d 0 2) (by simp) with h153 | h153
                      · linarith only [h153, h2, hlam]
                      · linarith only [h1, h153, hlam]
                    · have p127_0 := h127c.1
                      have p127_1 := h127c.2.1
                      have p127_2 := h127c.2.2.1
                      have p127_3 := h127c.2.2.2
                      linarith only [hlam, p127_0]
                · linarith only [h110, h120, h123, h124, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · linarith only [h110, h123, hc12, hlam, hphi, ht23, u3elo3]
          · linarith only [h1, h120, h2, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h160 | h160
      · linarith only [h1, h160, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h162 | h162
        · rcases m.htr 1 2 4 (by decide) (by decide) with h163 | h163
          · linarith only [h0, h1, h163, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h165 | h165
            · linarith only [h0, h160, h165, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h167 | h167
              · linarith only [h0, h1, h162, h167, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
              · linarith only [h0, h1, h162, h167, hc23, hlam, hphi, u3elo3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h170 | h170
          · linarith only [h1, h162, h170, hc02, hlam, hphi, ht23, u3elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h172 | h172
            · linarith only [h0, h160, h172, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h174 | h174
              · rcases m.htr 2 3 5 (by decide) (by decide) with h175 | h175
                · rcases m.htr 2 4 5 (by decide) (by decide) with h176 | h176
                  · rcases h2bigk with h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c | h177c
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h160, hc12, hlam, hphi, p177_1, u2elo4]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h160, h174, h176, hlam, p177_1]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h1, hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h160, hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h0, hlam, p177_1]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h162, hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h170, hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h172, hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [hc02, hlam, hphi, ht23, p177_1, u3elo2]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [hc12, hlam, hphi, ht23, p177_1, u3elo2]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h176, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p177_1, u3elo2, u5ehi2]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h0, h160, hc12, hlam, hphi, ht23, p177_1, u3elo2]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p177_1, u2elo3]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [hc12, hlam, hphi, p177_1, u2elo3]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h174, hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h0, h160, h174, hc12, hlam, hphi, ht23, p177_1, u3elo2]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p177_1, u2elo4]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [hc12, hlam, hphi, p177_1, u2elo4]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h175, hlam, p177_0]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [h176, hlam, p177_1]
                    · have p177_0 := h177c.1
                      have p177_1 := h177c.2.1
                      have p177_2 := h177c.2.2.1
                      have p177_3 := h177c.2.2.2
                      linarith only [hlam, p177_0]
                  · rcases h2bigk with h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c | h203c
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hc12, hlam, hphi, p203_1, u2elo0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h1, h175, h176, hlam, p203_1]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h1, hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h160, hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h0, hlam, p203_1]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h162, hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h170, hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h172, hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hc02, hlam, hphi, ht23, p203_1, u3elo2]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hc12, hlam, hphi, ht23, p203_1, u3elo2]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h0, h1, hc12, hlam, hphi, ht23, p203_1, u3elo2]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p203_1, u3elo2, u5ehi2]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p203_1, u2elo3]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h176, hc12, hc45, hlam, hphi, ht23, ht34, p203_1]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h174, hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h176, hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h0, hc12, hlam, hphi, p203_1, u2elo4]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hc12, hlam, hphi, p203_1, u2elo4]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h175, hlam, p203_0]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [h0, h1, h175, hc12, hlam, hphi, ht23, p203_1, u3elo2]
                    · have p203_0 := h203c.1
                      have p203_1 := h203c.2.1
                      have p203_2 := h203c.2.2.1
                      have p203_3 := h203c.2.2.2
                      linarith only [hlam, p203_0]
                · linarith only [h162, h175, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h162, h174, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h231 | h231
    · rcases m.htr 0 2 5 (by decide) (by decide) with h232 | h232
      · rcases m.htr 1 2 3 (by decide) (by decide) with h233 | h233
        · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
          · rcases m.htr 1 2 5 (by decide) (by decide) with h235 | h235
            · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
              · rcases m.htr 2 3 5 (by decide) (by decide) with h237 | h237
                · linarith only [h233, h237, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h239 | h239
                  · linarith only [h231, h239, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0, u5ehi4]
                  · rcases h2bigk with h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c | h241c
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h0, hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h0, h236, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p241_1, u2elo1]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      rcases p241_3 (m.d 0 2) (by simp) with h245 | h245
                      · rcases p241_3 (m.d 1 2) (by simp) with h246 | h246
                        · rcases p241_3 (m.d 2 3) (by simp) with h247 | h247
                          · linarith only [h232, h237, h247, hlam]
                          · linarith only [h236, h247, hlam]
                        · linarith only [h234, h246, hlam]
                      · linarith only [h245, hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p241_1, u2elo0, u5ehi2]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [hc02, hlam, hphi, p241_1, u2elo1]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h236, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p241_1, u2elo1]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      rcases p241_3 (m.d 0 2) (by simp) with h256 | h256
                      · linarith only [h0, h256, hlam]
                      · linarith only [h231, h256, hlam]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h236, h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p241_1, u2elo1]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h232, h237, hlam, p241_1]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h233, hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h232, h236, h237, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p241_1, u2elo0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h237, hlam, p241_1]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h231, hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h234, hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h236, hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h239, hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h232, hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h235, hlam, p241_0]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h0, h232, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p241_1, u2elo1]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [h0, h232, h236, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p241_1, u2elo1]
                    · have p241_0 := h241c.1
                      have p241_1 := h241c.2.1
                      have p241_2 := h241c.2.2.1
                      have p241_3 := h241c.2.2.2
                      linarith only [hlam, p241_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h275 | h275
                · linarith only [h236, h275, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h277 | h277
                  · linarith only [h0, h231, h277, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1, u5ehi4]
                  · rcases h2bigk with h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c | h279c
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h0, hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      rcases p279_3 (m.d 0 2) (by simp) with h282 | h282
                      · rcases p279_3 (m.d 1 2) (by simp) with h283 | h283
                        · rcases p279_3 (m.d 2 3) (by simp) with h284 | h284
                          · linarith only [h284, hlam, p279_0]
                          · rcases p279_3 (m.d 2 4) (by simp) with h286 | h286
                            · linarith only [h231, h286, hlam]
                            · linarith only [h236, h286, hlam]
                        · linarith only [h233, h283, hlam]
                      · linarith only [h282, hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      rcases p279_3 (m.d 0 2) (by simp) with h291 | h291
                      · rcases p279_3 (m.d 1 2) (by simp) with h292 | h292
                        · rcases p279_3 (m.d 2 3) (by simp) with h293 | h293
                          · linarith only [h236, h293, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p279_1, u3elo3]
                          · rcases p279_3 (m.d 2 4) (by simp) with h295 | h295
                            · linarith only [h295, hlam, p279_0]
                            · rcases p279_3 (m.d 2 5) (by simp) with h297 | h297
                              · linarith only [h232, h297, hlam]
                              · linarith only [h277, h297, hlam]
                        · linarith only [h234, h292, hlam]
                      · linarith only [h291, hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p279_1, u2elo0, u5ehi2]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [hc02, hlam, hphi, p279_1, u2elo1]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      rcases p279_3 (m.d 0 2) (by simp) with h305 | h305
                      · linarith only [h0, h305, hlam]
                      · linarith only [h232, h275, h305, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4, u5ehi2]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      rcases p279_3 (m.d 0 2) (by simp) with h308 | h308
                      · linarith only [h0, h308, hlam]
                      · linarith only [h231, h308, hlam]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [hlam, hphi, ht01, ht0b, ht12, ht5b, p279_1, u2elo1, u5ehi2]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [hc02, hlam, hphi, p279_1, u2elo2]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h233, hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h236, hlam, p279_1]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h275, hlam, p279_1]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h231, hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h234, hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h234, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p279_1, u2elo1]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h277, hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h232, hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h235, hlam, p279_0]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h0, h232, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p279_1, u2elo1]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [h0, h232, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p279_1, u2elo1]
                    · have p279_0 := h279c.1
                      have p279_1 := h279c.2.1
                      have p279_2 := h279c.2.2.1
                      have p279_3 := h279c.2.2.2
                      linarith only [hlam, p279_0]
            · linarith only [h0, h232, h235, hlam]
          · linarith only [h0, h232, h234, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
        · linarith only [h0, h232, h233, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
        · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
          · rcases m.htr 1 2 5 (by decide) (by decide) with h332 | h332
            · linarith only [h232, h332, hc02, hlam, hphi, u2elo1]
            · linarith only [h0, h332, hc01, hlam, hphi, ht12, u2elo4]
          · linarith only [h0, h331, hc01, hlam, hphi, ht12, u2elo3]
        · linarith only [h0, h330, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h337 | h337
      · linarith only [h231, h337, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3, u5ehi2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h339 | h339
        · rcases m.htr 1 2 4 (by decide) (by decide) with h340 | h340
          · linarith only [h231, h340, hc02, hlam, hphi, u2elo1]
          · linarith only [h0, h340, hc01, hlam, hphi, ht12, u2elo3]
        · linarith only [h0, h339, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
