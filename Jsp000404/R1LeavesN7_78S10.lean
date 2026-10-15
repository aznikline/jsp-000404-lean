import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_21_14_M_IR_L_R (m : N7Model)
    (hb1 : CMSig2_7_M_IR m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.2.1
  have h1bigk := hb1.2.2.2
  have h4ehi := hb4.1
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
  have u1ehi3 := h1ehi (m.d 1 4) (by simp)
  have u1ehi4 := h1ehi (m.d 1 5) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h12 | h12
                        · linarith only [h0, h12, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h10, h12, h4, h7, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                      · linarith only [h0, h15, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h17 | h17
                        · linarith only [h17, h9, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · rcases h1bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h17, h4, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p19_1, u4ehi3]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h17, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p19_1, u4ehi3]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            rcases p19_3 (m.d 0 1) (by simp) with h23 | h23
                            · rcases p19_3 (m.d 1 2) (by simp) with h24 | h24
                              · linarith only [h0, h24, hlam]
                              · linarith only [h24, h5, hlam]
                            · linarith only [h23, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            rcases p19_3 (m.d 0 1) (by simp) with h28 | h28
                            · rcases p19_3 (m.d 1 2) (by simp) with h29 | h29
                              · linarith only [h0, h29, hlam]
                              · linarith only [h29, h6, hlam]
                            · linarith only [h28, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h0, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h15, h17, h8, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19_1]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h0, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p19_1, u1ehi3]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p19_1, u1ehi3]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h1, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h4, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [hc13, hlam, hphi, p19_1, u1ehi3]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p19_1, u1ehi3]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h2, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h5, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h7, hlam, p19_1]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h9, hlam, p19_1]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h3, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h6, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [h8, hlam, p19_0]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [hc15, hlam, hphi, p19_1, u1ehi3]
                          · have p19_0 := h19c.1
                            have p19_1 := h19c.2.1
                            have p19_2 := h19c.2.2.1
                            have p19_3 := h19c.2.2.2
                            linarith only [hlam, p19_0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                    · linarith only [h53, h7, h8, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h55 | h55
                      · linarith only [h0, h4, h55, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h55, h7, h8, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h58 | h58
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                      · linarith only [h60, h7, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                        · rcases h1bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p63_1, u4ehi2]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h58, h62, hc01, hlam, hphi, ht0b, ht45, ht5b, p63_1, u4ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h58, h62, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p63_1, u4ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            rcases p63_3 (m.d 0 1) (by simp) with h68 | h68
                            · rcases p63_3 (m.d 1 2) (by simp) with h69 | h69
                              · linarith only [h0, h69, hlam]
                              · linarith only [h6, h69, hlam]
                            · linarith only [h68, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h0, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h58, h62, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p63_1, u4ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h0, h58, h62, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p63_1, u4ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h0, h58, h62, h7, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, p63_1, u1ehi4, u4ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h1, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h4, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h7, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h7, hc34, hlam, hphi, ht12, ht23, p63_1, u1ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h2, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h5, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h58, h62, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p63_1, u4ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h0, h5, h58, h62, h7, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, p63_1, u1ehi4, u4ehi4]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h3, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h6, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h58, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [h59, hlam, p63_0]
                          · have p63_0 := h63c.1
                            have p63_1 := h63c.2.1
                            have p63_2 := h63c.2.2.1
                            have p63_3 := h63c.2.2.2
                            linarith only [hlam, p63_0]
                        · linarith only [h62, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · linarith only [h58, h59, h7, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                      · linarith only [h7, h96, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h98 | h98
                        · rcases h1bigk with h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c | h99c
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p99_1, u4ehi2]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            rcases p99_3 (m.d 0 1) (by simp) with h102 | h102
                            · rcases p99_3 (m.d 1 2) (by simp) with h103 | h103
                              · linarith only [h0, h103, hlam]
                              · linarith only [h103, h4, hlam]
                            · linarith only [h102, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h95, hc01, hlam, hphi, ht0b, ht45, ht5b, p99_1, u4ehi4]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            rcases p99_3 (m.d 0 1) (by simp) with h108 | h108
                            · rcases p99_3 (m.d 1 2) (by simp) with h109 | h109
                              · linarith only [h0, h109, hlam]
                              · linarith only [h109, h6, hlam]
                            · linarith only [h108, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h0, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hc12, hlam, hphi, p99_1, u1ehi2]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h0, h95, hc01, hlam, hphi, ht0b, ht45, ht5b, p99_1, u4ehi4]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h0, h58, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h1, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h4, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h7, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h58, hlam, p99_1]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h2, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h5, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hc14, hlam, hphi, p99_1, u1ehi2]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h0, h5, h58, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p99_1, u1ehi2]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h3, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h6, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hc15, hlam, hphi, p99_1, u1ehi2]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [h95, hlam, p99_0]
                          · have p99_0 := h99c.1
                            have p99_1 := h99c.2.1
                            have p99_2 := h99c.2.2.1
                            have p99_3 := h99c.2.2.2
                            linarith only [hlam, p99_0]
                        · linarith only [h7, h98, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h134 | h134
                      · linarith only [h134, h4, h7, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h136 | h136
                        · linarith only [h136, h95, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h136, h7, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h139 | h139
                · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
                  · linarith only [h140, h4, h6, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h142 | h142
                    · linarith only [h139, h142, h4, h6, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                      · linarith only [h144, h4, h6, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h139, h140, h144, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                  · linarith only [h147, h4, h6, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h149 | h149
                    · linarith only [h149, h5, h6, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                      · linarith only [h139, h151, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h153 | h153
                        · linarith only [h149, h153, hc34, hlam, hphi, ht12, ht23, u1ehi3]
                        · linarith only [h139, h153, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
              · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                · linarith only [h157, h4, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h159 | h159
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h160 | h160
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                      · linarith only [h157, h161, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h163 | h163
                        · rcases h1bigk with h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c | h164c
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h159, h163, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p164_1, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h159, h163, hc01, hlam, hphi, ht0b, ht45, ht5b, p164_1, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h159, h163, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, p164_1, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            rcases p164_3 (m.d 0 1) (by simp) with h169 | h169
                            · rcases p164_3 (m.d 1 2) (by simp) with h170 | h170
                              · linarith only [h0, h170, hlam]
                              · linarith only [h156, h170, hlam]
                            · linarith only [h169, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h0, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h159, h161, h163, h5, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p164_1, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h5, hlam, p164_1]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h161, h5, hc34, hlam, hphi, ht12, ht23, p164_1, u1ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h1, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h4, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h157, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hc13, hlam, hphi, p164_1, u1ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h2, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hc14, hlam, hphi, p164_1, u1ehi1]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p164_1, u1ehi2]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h159, h161, h163, h2, h4, h5, hc01, hc34, hlam, hphi, ht0b, ht12, ht23, ht45, ht5b, p164_1, u1ehi4, u4ehi4]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h3, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h156, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h159, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [h160, hlam, p164_0]
                          · have p164_0 := h164c.1
                            have p164_1 := h164c.2.1
                            have p164_2 := h164c.2.2.1
                            have p164_3 := h164c.2.2.2
                            linarith only [hlam, p164_0]
                        · linarith only [h161, h163, h4, h5, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h159, h160, h4, h5, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h196 | h196
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h197 | h197
                      · linarith only [h197, h2, h4, h5, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h199 | h199
                        · rcases h1bigk with h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            rcases p200_3 (m.d 0 1) (by simp) with h202 | h202
                            · rcases p200_3 (m.d 1 2) (by simp) with h203 | h203
                              · linarith only [h203, hlam, p200_0]
                              · rcases p200_3 (m.d 1 3) (by simp) with h205 | h205
                                · linarith only [h1, h205, hlam]
                                · rcases p200_3 (m.d 1 4) (by simp) with h207 | h207
                                  · linarith only [h2, h207, hlam]
                                  · linarith only [h207, h5, hlam]
                            · linarith only [h202, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            rcases p200_3 (m.d 0 1) (by simp) with h211 | h211
                            · rcases p200_3 (m.d 1 2) (by simp) with h212 | h212
                              · linarith only [h0, h212, hlam]
                              · linarith only [h212, h4, hlam]
                            · linarith only [h211, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h196, hc01, hlam, hphi, ht0b, ht45, ht5b, p200_1, u4ehi4]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            rcases p200_3 (m.d 0 1) (by simp) with h217 | h217
                            · rcases p200_3 (m.d 1 2) (by simp) with h218 | h218
                              · linarith only [h0, h218, hlam]
                              · linarith only [h156, h218, hlam]
                            · linarith only [h217, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h0, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h197, h5, hc13, hc34, hlam, hphi, p200_1]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h5, hlam, p200_1]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h197, h5, hc34, hlam, hphi, ht12, ht23, p200_1, u1ehi4]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h1, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h4, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h157, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h159, hlam, p200_1]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h2, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [hc14, hlam, hphi, p200_1, u1ehi1]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p200_1, u1ehi2]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h159, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p200_1, u1ehi2]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h3, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h156, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h156, hc12, hlam, hphi, p200_1, u1ehi2]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [h196, hlam, p200_0]
                          · have p200_0 := h200c.1
                            have p200_1 := h200c.2.1
                            have p200_2 := h200c.2.2.1
                            have p200_3 := h200c.2.2.2
                            linarith only [hlam, p200_0]
                        · linarith only [h197, h199, h4, h5, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h156, h196, h5, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
                · linarith only [h244, h4, h5, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h246 | h246
                  · linarith only [h156, h246, h4, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h248 | h248
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                      · linarith only [h244, h249, hc23, hlam, hphi, ht12, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h251 | h251
                        · rcases h1bigk with h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            rcases p252_3 (m.d 0 1) (by simp) with h254 | h254
                            · rcases p252_3 (m.d 1 2) (by simp) with h255 | h255
                              · linarith only [h255, hlam, p252_0]
                              · rcases p252_3 (m.d 1 3) (by simp) with h257 | h257
                                · linarith only [h1, h257, hlam]
                                · rcases p252_3 (m.d 1 4) (by simp) with h259 | h259
                                  · linarith only [h2, h259, hlam]
                                  · linarith only [h259, h5, hlam]
                            · linarith only [h254, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            rcases p252_3 (m.d 0 1) (by simp) with h263 | h263
                            · rcases p252_3 (m.d 1 2) (by simp) with h264 | h264
                              · linarith only [h0, h264, hlam]
                              · linarith only [h264, h4, hlam]
                            · linarith only [h263, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h248, hc01, hlam, hphi, ht0b, ht45, ht5b, p252_1, u4ehi4]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            rcases p252_3 (m.d 0 1) (by simp) with h269 | h269
                            · rcases p252_3 (m.d 1 2) (by simp) with h270 | h270
                              · linarith only [h0, h270, hlam]
                              · rcases p252_3 (m.d 1 3) (by simp) with h272 | h272
                                · linarith only [h1, h272, hlam]
                                · rcases p252_3 (m.d 1 4) (by simp) with h274 | h274
                                  · linarith only [h2, h274, hlam]
                                  · linarith only [h248, h274, hlam]
                            · linarith only [h269, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h0, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hc12, hlam, hphi, p252_1, u1ehi2]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h5, hlam, p252_1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h156, hlam, p252_1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h1, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h4, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h244, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h246, hlam, p252_1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h2, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hc14, hlam, hphi, p252_1, u1ehi1]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p252_1, u1ehi2]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hc14, hlam, hphi, p252_1, u1ehi4]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h3, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h4, hc15, hlam, hphi, p252_1, u1ehi2]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p252_1, u1ehi2]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [h248, hlam, p252_0]
                          · have p252_0 := h252c.1
                            have p252_1 := h252c.2.1
                            have p252_2 := h252c.2.2.1
                            have p252_3 := h252c.2.2.2
                            linarith only [hlam, p252_0]
                        · linarith only [h249, h251, h4, h5, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h299 | h299
                      · linarith only [h244, h299, h4, hc12, hlam, hphi, u1ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h301 | h301
                        · linarith only [h248, h301, h4, h5, hc23, hc34, hlam, hphi]
                        · linarith only [h244, h301, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
            · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
              · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                        · linarith only [h304, h309, h310, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h2, h308, h310, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h304, h309, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h314 | h314
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h315 | h315
                        · linarith only [h304, h308, h314, h315, hc12, hlam, hphi, u1ehi3]
                        · rcases h1bigk with h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c | h317c
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h304, hc01, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi2]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h304, h314, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p317_1, u4ehi3]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            rcases p317_3 (m.d 0 1) (by simp) with h321 | h321
                            · rcases p317_3 (m.d 1 2) (by simp) with h322 | h322
                              · linarith only [h0, h322, hlam]
                              · linarith only [h304, h322, hlam]
                            · linarith only [h321, hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            rcases p317_3 (m.d 0 1) (by simp) with h326 | h326
                            · rcases p317_3 (m.d 1 2) (by simp) with h327 | h327
                              · linarith only [h0, h327, hlam]
                              · linarith only [h305, h327, hlam]
                            · linarith only [h326, hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h0, hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h4, hlam, p317_1]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [hc12, hlam, hphi, p317_1, u1ehi3]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h4, hc23, hlam, hphi, ht12, p317_1, u1ehi4]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h1, hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h1, h305, hc01, hc25, hlam, hphi, ht0b, ht5b, p317_1]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p317_1, u1ehi3]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p317_1, u1ehi4]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h2, hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h304, hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h306, hlam, p317_1]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h308, hlam, p317_1]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h3, hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h305, hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [h307, hlam, p317_0]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [hc15, hlam, hphi, p317_1, u1ehi3]
                          · have p317_0 := h317c.1
                            have p317_1 := h317c.2.1
                            have p317_2 := h317c.2.2.1
                            have p317_3 := h317c.2.2.2
                            linarith only [hlam, p317_0]
                      · linarith only [h314, h4, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · linarith only [h305, h307, h4, hlam]
                · linarith only [h304, h306, h4, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h354 | h354
                · rcases m.htr 1 3 5 (by decide) (by decide) with h355 | h355
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h356 | h356
                    · linarith only [h304, h305, h356, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h358 | h358
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                        · linarith only [h356, h358, h359, hc24, hlam, hphi, ht12, u1ehi3]
                        · rcases h1bigk with h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c | h361c
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h304, hc01, hlam, hphi, ht0b, ht45, ht5b, p361_1, u4ehi2]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h304, h358, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, p361_1, u4ehi3]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            rcases p361_3 (m.d 0 1) (by simp) with h365 | h365
                            · rcases p361_3 (m.d 1 2) (by simp) with h366 | h366
                              · linarith only [h0, h366, hlam]
                              · linarith only [h304, h366, hlam]
                            · linarith only [h365, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h304, h305, h358, hc01, hlam, hphi, ht0b, ht45, ht5b, p361_1, u4ehi3]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h0, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h4, hlam, p361_1]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hc12, hlam, hphi, p361_1, u1ehi3]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h305, hlam, p361_1]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h1, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p361_1, u1ehi1]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p361_1, u1ehi3]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h1, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p361_1, u1ehi4]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h2, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h304, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h354, hlam, p361_1]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h356, hlam, p361_1]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h3, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h304, h358, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p361_1, u4ehi3]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h355, hlam, p361_0]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [h1, h355, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p361_1, u1ehi3]
                          · have p361_0 := h361c.1
                            have p361_1 := h361c.2.1
                            have p361_2 := h361c.2.2.1
                            have p361_3 := h361c.2.2.2
                            linarith only [hlam, p361_0]
                      · linarith only [h304, h358, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h392 | h392
                    · linarith only [h304, h305, h392, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h394 | h394
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h395 | h395
                        · linarith only [h304, h392, h394, h395, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h304, h355, h395, h4, hc45, hlam, hphi, u4ehi2]
                      · linarith only [h304, h394, h4, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h304, h354, h4, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h400 | h400
              · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                · rcases m.htr 1 3 5 (by decide) (by decide) with h402 | h402
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h404 | h404
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h405 | h405
                        · linarith only [h1, h401, h405, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h2, h403, h405, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h4, h404, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h304, h400, h403, hlam]
                  · linarith only [h4, h400, h402, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h412 | h412
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h413 | h413
                      · linarith only [h4, h401, h413, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h4, h400, h413, hc34, hlam, hphi, ht12, ht23, u1ehi4]
                    · linarith only [h304, h400, h412, hlam]
                  · linarith only [h4, h400, h411, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h418 | h418
                · rcases m.htr 1 3 5 (by decide) (by decide) with h419 | h419
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h422 | h422
                        · linarith only [h1, h418, h422, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h2, h420, h422, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · linarith only [h4, h421, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h426 | h426
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h427 | h427
                        · linarith only [h1, h418, h427, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases h1bigk with h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c | h429c
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            rcases p429_3 (m.d 0 1) (by simp) with h431 | h431
                            · rcases p429_3 (m.d 1 2) (by simp) with h432 | h432
                              · linarith only [h432, hlam, p429_0]
                              · rcases p429_3 (m.d 1 3) (by simp) with h434 | h434
                                · linarith only [h1, h434, hlam]
                                · linarith only [h4, h434, hlam]
                            · linarith only [h431, hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h419, h427, hc01, hlam, hphi, ht0b, ht45, ht5b, p429_1, u4ehi3]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            rcases p429_3 (m.d 0 1) (by simp) with h439 | h439
                            · rcases p429_3 (m.d 1 2) (by simp) with h440 | h440
                              · linarith only [h0, h440, hlam]
                              · rcases p429_3 (m.d 1 3) (by simp) with h442 | h442
                                · linarith only [h1, h442, hlam]
                                · linarith only [h418, h442, hlam]
                            · linarith only [h439, hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            rcases p429_3 (m.d 0 1) (by simp) with h446 | h446
                            · rcases p429_3 (m.d 1 2) (by simp) with h447 | h447
                              · linarith only [h0, h447, hlam]
                              · rcases p429_3 (m.d 1 3) (by simp) with h449 | h449
                                · linarith only [h1, h449, hlam]
                                · linarith only [h419, h449, hlam]
                            · linarith only [h446, hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h0, hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h4, hlam, p429_1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h304, hlam, p429_1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h400, hlam, p429_1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h1, hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [hc13, hlam, hphi, p429_1, u1ehi1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h1, h304, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p429_1, u1ehi1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h1, h304, h420, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p429_1, u1ehi1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h2, hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [hc14, hlam, hphi, p429_1, u1ehi1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h418, hlam, p429_1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h420, hlam, p429_1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h3, hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h3, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p429_1, u1ehi1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h419, hlam, p429_0]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [h1, h419, hc01, hlam, hphi, ht0b, ht45, ht5b, p429_1, u4ehi1]
                          · have p429_0 := h429c.1
                            have p429_1 := h429c.2.1
                            have p429_2 := h429c.2.2.1
                            have p429_3 := h429c.2.2.2
                            linarith only [hlam, p429_0]
                      · linarith only [h4, h426, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
                    · linarith only [h418, h419, h474, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h476 | h476
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h477 | h477
                        · linarith only [h418, h419, h474, h477, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                        · linarith only [h418, h419, h477, hc45, hlam, hphi, u4ehi3]
                      · linarith only [h418, h419, h476, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h481 | h481
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h482 | h482
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h483 | h483
                      · linarith only [h418, h483, hc23, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h4, h483, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · linarith only [h418, h481, h482, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h487 | h487
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h488 | h488
                      · linarith only [h418, h488, hc23, hlam, hphi, ht12, u1ehi2]
                      · linarith only [h4, h488, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h491 | h491
                      · linarith only [h4, h418, h491, hc23, hlam, hphi, ht12, u1ehi1]
                      · linarith only [h4, h491, hc34, hlam, hphi, ht12, ht23, u1ehi1]
        · linarith only [h0, h3, hc15, hlam, hphi, u1ehi1]
      · linarith only [h0, h2, hc14, hlam, hphi, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h497 | h497
    · linarith only [h0, h497, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h499 | h499
      · linarith only [h0, h499, hc12, hlam, hphi, u1ehi3]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h501 | h501
        · linarith only [h0, h501, hc12, hlam, hphi, u1ehi4]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
          · rcases m.htr 1 2 4 (by decide) (by decide) with h504 | h504
            · rcases m.htr 1 2 5 (by decide) (by decide) with h505 | h505
              · rcases m.htr 1 3 4 (by decide) (by decide) with h506 | h506
                · rcases m.htr 1 3 5 (by decide) (by decide) with h507 | h507
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h508 | h508
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h509 | h509
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h510 | h510
                        · linarith only [h503, h509, h510, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · rcases h1bigk with h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c | h512c
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h0, hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h497, hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h499, hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h501, hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hc12, hlam, hphi, p512_1, u1ehi0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h506, h508, h510, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p512_1, u4ehi3]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h508, h510, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p512_1, u4ehi3]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hc12, hlam, hphi, p512_1, u1ehi4]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hc13, hlam, hphi, p512_1, u1ehi0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h503, hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h503, h508, h510, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p512_1, u4ehi3]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h501, h503, hc12, hlam, hphi, p512_1, u1ehi0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hc14, hlam, hphi, p512_1, u1ehi0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h504, hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h506, hlam, p512_1]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h501, h503, h506, hc12, hlam, hphi, p512_1, u1ehi0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hc15, hlam, hphi, p512_1, u1ehi0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h505, hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h507, hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [h508, hlam, p512_0]
                          · have p512_0 := h512c.1
                            have p512_1 := h512c.2.1
                            have p512_2 := h512c.2.2.1
                            have p512_3 := h512c.2.2.2
                            linarith only [hlam, p512_0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h538 | h538
                        · rcases h1bigk with h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c | h539c
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h0, hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h497, hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h499, hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h501, hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hc12, hlam, hphi, p539_1, u1ehi0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h506, h509, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p539_1]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hc12, hlam, hphi, p539_1, u1ehi3]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h501, hc12, hlam, hphi, p539_1, u1ehi0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hc13, hlam, hphi, p539_1, u1ehi0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h503, hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h499, h503, hc12, hlam, hphi, p539_1, u1ehi0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h501, h503, hc12, hlam, hphi, p539_1, u1ehi0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hc14, hlam, hphi, p539_1, u1ehi0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h504, hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h506, hlam, p539_1]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h501, h503, h506, hc12, hlam, hphi, p539_1, u1ehi0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hc15, hlam, hphi, p539_1, u1ehi0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h505, hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h507, hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [h508, hlam, p539_0]
                          · have p539_0 := h539c.1
                            have p539_1 := h539c.2.1
                            have p539_2 := h539c.2.2.1
                            have p539_3 := h539c.2.2.2
                            linarith only [hlam, p539_0]
                        · rcases h1bigk with h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c | h565c
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h0, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h497, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h499, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h501, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hc12, hlam, hphi, p565_1, u1ehi0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h506, h508, h509, h538, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p565_1]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h508, h509, h538, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p565_1]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hc12, hlam, hphi, p565_1, u1ehi4]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hc13, hlam, hphi, p565_1, u1ehi0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h503, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h503, h508, h509, h538, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p565_1]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h501, h503, hc12, hlam, hphi, p565_1, u1ehi0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hc14, hlam, hphi, p565_1, u1ehi0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h504, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h506, hlam, p565_1]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h501, h503, h506, hc12, hlam, hphi, p565_1, u1ehi0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hc15, hlam, hphi, p565_1, u1ehi0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h505, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h507, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [h508, hlam, p565_0]
                          · have p565_0 := h565c.1
                            have p565_1 := h565c.2.1
                            have p565_2 := h565c.2.2.1
                            have p565_3 := h565c.2.2.2
                            linarith only [hlam, p565_0]
                    · linarith only [h499, h508, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi0]
                  · linarith only [h497, h507, hc35, hlam, hphi, ht12, ht23, u1ehi0]
                · linarith only [h497, h506, hc34, hlam, hphi, ht12, ht23, u1ehi0]
              · linarith only [h0, h505, hc25, hlam, hphi, ht12, u1ehi0]
            · linarith only [h497, h503, h504, hc24, hlam, hphi, ht12, u1ehi0]
          · linarith only [h0, h503, hc23, hlam, hphi, ht12, u1ehi0]

end R2N4
