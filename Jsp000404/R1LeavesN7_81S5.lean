import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_23_L_R_M_IR (m : N7Model)
    (hb1 : CMSig1_7_L_R m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h1ehi := hb1.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u1ehi0 := h1ehi (m.d 0 1) (by simp)
  have u1ehi1 := h1ehi (m.d 1 2) (by simp)
  have u1ehi2 := h1ehi (m.d 1 3) (by simp)
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
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 4 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h5, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h5, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                · linarith only [h0, h12, h2, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                  · linarith only [h14, h6, hc23, hlam, hphi, ht12, u1ehi2]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h12, h16, h5, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                      · rcases h3bigk with h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c | h19c
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          rcases p19_3 (m.d 0 3) (by simp) with h21 | h21
                          · rcases p19_3 (m.d 1 3) (by simp) with h22 | h22
                            · linarith only [h1, h22, hlam]
                            · rcases p19_3 (m.d 2 3) (by simp) with h24 | h24
                              · linarith only [h2, h24, hlam]
                              · rcases p19_3 (m.d 3 4) (by simp) with h26 | h26
                                · linarith only [h26, h3, hlam]
                                · linarith only [h26, h6, hlam]
                          · linarith only [h1, h21, hlam]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          rcases p19_3 (m.d 0 3) (by simp) with h30 | h30
                          · rcases p19_3 (m.d 1 3) (by simp) with h31 | h31
                            · linarith only [h1, h31, hlam]
                            · linarith only [h31, h5, hlam]
                          · linarith only [h2, h30, hlam]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h0, h12, h18, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p19_1, u1ehi2]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h0, h12, h2, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p19_1, u1ehi2]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h1, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h12, h18, hc34, hlam, hphi, p19_1, u3ehi2]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h6, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h12, hlam, p19_0]
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
                          linarith only [hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h14, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h16, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h3, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1, u3ehi1]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1, u3ehi2]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h0, h2, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1, u3ehi4]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h4, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p19_1, u1ehi2]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p19_1, u3ehi2]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [h18, hlam, p19_0]
                        · have p19_0 := h19c.1
                          have p19_1 := h19c.2.1
                          have p19_2 := h19c.2.2.1
                          have p19_3 := h19c.2.2.2
                          linarith only [hlam, p19_0]
                      · linarith only [h18, h6, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h58 | h58
              · rcases m.htr 1 3 5 (by decide) (by decide) with h59 | h59
                · rcases m.htr 2 3 4 (by decide) (by decide) with h60 | h60
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h61 | h61
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h62 | h62
                      · rcases h3bigk with h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c | h63c
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h0, h2, h58, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi4]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h0, h2, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p63_1, u1ehi1]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          rcases p63_3 (m.d 0 3) (by simp) with h67 | h67
                          · rcases p63_3 (m.d 1 3) (by simp) with h68 | h68
                            · linarith only [h1, h68, hlam]
                            · linarith only [h58, h68, hlam]
                          · linarith only [h67, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          rcases p63_3 (m.d 0 3) (by simp) with h72 | h72
                          · rcases p63_3 (m.d 1 3) (by simp) with h73 | h73
                            · linarith only [h1, h73, hlam]
                            · linarith only [h59, h73, hlam]
                          · linarith only [h72, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h1, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h5, hlam, p63_1]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h1, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi4]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h0, h2, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi4]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h2, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi1]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h0, h2, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi4]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p63_1, u3ehi4]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h3, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h58, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h60, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h58, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p63_1, u3ehi4]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h4, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h59, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h61, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [h62, hlam, p63_0]
                        · have p63_0 := h63c.1
                          have p63_1 := h63c.2.1
                          have p63_2 := h63c.2.2.1
                          have p63_3 := h63c.2.2.2
                          linarith only [hlam, p63_0]
                      · rcases h3bigk with h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c | h97c
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, h2, h59, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p97_1, u3ehi3]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, h2, h5, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p97_1, u1ehi1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 3) (by simp) with h101 | h101
                          · rcases p97_3 (m.d 1 3) (by simp) with h102 | h102
                            · linarith only [h1, h102, hlam]
                            · linarith only [h102, h58, hlam]
                          · linarith only [h101, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          rcases p97_3 (m.d 0 3) (by simp) with h106 | h106
                          · rcases p97_3 (m.d 1 3) (by simp) with h107 | h107
                            · linarith only [h1, h107, hlam]
                            · linarith only [h107, h59, hlam]
                          · linarith only [h106, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h1, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h5, hlam, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p97_1, u3ehi3]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h1, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p97_1, u3ehi3]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h2, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p97_1, u1ehi2]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p97_1, u3ehi3]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, h2, h62, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p97_1, u3ehi3]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h3, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h58, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h60, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h62, hlam, p97_1]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h4, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h59, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h61, hlam, p97_0]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [h0, h2, h5, h59, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p97_1, u1ehi1, u3ehi3]
                        · have p97_0 := h97c.1
                          have p97_1 := h97c.2.1
                          have p97_2 := h97c.2.2.1
                          have p97_3 := h97c.2.2.2
                          linarith only [hlam, p97_0]
                    · linarith only [h5, h59, h61, hlam]
                  · linarith only [h5, h60, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h58, h59, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h134 | h134
                · linarith only [h0, h134, h2, h3, h58, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h136 | h136
                  · linarith only [h0, h136, h2, h5, h58, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u1ehi1]
                  · linarith only [h136, h5, hc34, hlam, hphi, ht12, ht23, u1ehi1]
          · linarith only [h3, h4, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h140 | h140
          · linarith only [h140, h3, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
            · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
              · linarith only [h1, h143, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h145 | h145
                · linarith only [h1, h140, h145, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h147 | h147
                  · linarith only [h0, h142, h147, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h149 | h149
                    · linarith only [h1, h140, h142, h149, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
                      · rcases h3bigk with h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h140, h151, hc34, hlam, hphi, ht12, ht23, p152_1, u1ehi2]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h140, h151, hc34, hlam, hphi, p152_1, u3ehi2]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h3, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h140, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h1, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1, u3ehi2]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h143, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h145, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h2, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h142, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h147, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h149, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hc34, hlam, hphi, p152_1, u3ehi0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hc34, hlam, hphi, ht12, ht23, p152_1, u1ehi2]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hc34, hlam, hphi, p152_1, u3ehi2]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hc34, hlam, hphi, p152_1, u3ehi4]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h1, hc35, hlam, hphi, ht12, ht23, p152_1, u1ehi2]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hc35, hlam, hphi, ht12, ht23, p152_1, u1ehi2]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hc35, hlam, hphi, p152_1, u3ehi2]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [h151, hlam, p152_0]
                        · have p152_0 := h152c.1
                          have p152_1 := h152c.2.1
                          have p152_2 := h152c.2.2.1
                          have p152_3 := h152c.2.2.2
                          linarith only [hlam, p152_0]
                      · linarith only [h1, h151, h3, hc45, hlam, hphi, ht12, ht23, ht34, u1ehi2]
            · linarith only [h142, h2, h3, hc34, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h180 | h180
        · rcases m.htr 0 3 5 (by decide) (by decide) with h181 | h181
          · rcases m.htr 1 2 3 (by decide) (by decide) with h182 | h182
            · linarith only [h0, h182, h2, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h184 | h184
              · rcases m.htr 1 3 5 (by decide) (by decide) with h185 | h185
                · rcases m.htr 2 3 4 (by decide) (by decide) with h186 | h186
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h187 | h187
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h188 | h188
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
                          linarith only [h184, h188, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p189_1, u3ehi4]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h2, hlam, p189_1]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          rcases p189_3 (m.d 0 3) (by simp) with h193 | h193
                          · rcases p189_3 (m.d 1 3) (by simp) with h194 | h194
                            · linarith only [h1, h194, hlam]
                            · linarith only [h184, h194, hlam]
                          · linarith only [h193, hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          rcases p189_3 (m.d 0 3) (by simp) with h198 | h198
                          · rcases p189_3 (m.d 1 3) (by simp) with h199 | h199
                            · linarith only [h1, h199, hlam]
                            · linarith only [h185, h199, hlam]
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
                          linarith only [h182, hlam, p189_1]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h1, h188, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p189_1, u3ehi4]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p189_1, u3ehi4]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht12, p189_1, u1ehi2]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p189_1, u1ehi2]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          rcases p189_3 (m.d 0 3) (by simp) with h211 | h211
                          · linarith only [h2, h211, hlam]
                          · linarith only [h180, h211, hlam]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          rcases p189_3 (m.d 0 3) (by simp) with h214 | h214
                          · linarith only [h2, h214, hlam]
                          · linarith only [h181, h214, hlam]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h180, hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h184, hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h186, hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h1, h184, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p189_1, u3ehi4]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h181, hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h185, hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h187, hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [h188, hlam, p189_0]
                        · have p189_0 := h189c.1
                          have p189_1 := h189c.2.1
                          have p189_2 := h189c.2.2.1
                          have p189_3 := h189c.2.2.2
                          linarith only [hlam, p189_0]
                      · rcases h3bigk with h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h2, hc23, hlam, hphi, ht12, p227_1, u1ehi2]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h2, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          rcases p227_3 (m.d 0 3) (by simp) with h231 | h231
                          · rcases p227_3 (m.d 1 3) (by simp) with h232 | h232
                            · linarith only [h1, h232, hlam]
                            · linarith only [h184, h232, hlam]
                          · linarith only [h231, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          rcases p227_3 (m.d 0 3) (by simp) with h236 | h236
                          · rcases p227_3 (m.d 1 3) (by simp) with h237 | h237
                            · linarith only [h1, h237, hlam]
                            · linarith only [h185, h237, hlam]
                          · linarith only [h236, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h182, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1, u3ehi3]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, h188, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1, u3ehi3]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, hc23, hlam, hphi, ht12, p227_1, u1ehi2]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hc23, hlam, hphi, ht12, p227_1, u1ehi2]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          rcases p227_3 (m.d 0 3) (by simp) with h249 | h249
                          · linarith only [h2, h249, hlam]
                          · linarith only [h180, h249, hlam]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          rcases p227_3 (m.d 0 3) (by simp) with h252 | h252
                          · linarith only [h2, h252, hlam]
                          · linarith only [h181, h252, hlam]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h180, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h184, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h186, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h188, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h181, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h185, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h187, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, h185, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p227_1, u3ehi3]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                    · linarith only [h1, h185, h187, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h0, h186, h2, hc34, hlam, hphi, ht12, ht23, u1ehi1]
                · linarith only [h184, h185, hc35, hlam, hphi, u3ehi3]
              · linarith only [h180, h184, h2, hc23, hlam, hphi, ht12, u1ehi2]
          · linarith only [h180, h181, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h270 | h270
          · linarith only [h180, h270, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h272 | h272
            · linarith only [h0, h2, h272, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h274 | h274
              · linarith only [h1, h180, h274, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h276 | h276
                · linarith only [h0, h2, h270, h276, hc13, hlam, hphi, u1ehi1]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h278 | h278
                  · linarith only [h0, h180, h2, h278, hc23, hlam, hphi, ht12, u1ehi1]
                  · linarith only [h0, h2, h278, hc34, hlam, hphi, ht12, ht23, u1ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, u1ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h282 | h282
    · linarith only [h0, h282, hc12, hlam, hphi, u1ehi2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h284 | h284
      · rcases m.htr 0 3 4 (by decide) (by decide) with h285 | h285
        · rcases m.htr 0 3 5 (by decide) (by decide) with h286 | h286
          · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
            · rcases m.htr 1 3 4 (by decide) (by decide) with h288 | h288
              · rcases m.htr 1 3 5 (by decide) (by decide) with h289 | h289
                · rcases m.htr 2 3 4 (by decide) (by decide) with h290 | h290
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h291 | h291
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h292 | h292
                      · rcases h3bigk with h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c | h293c
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h282, hlam, p293_1]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h290, h292, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p293_1, u3ehi4]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          rcases p293_3 (m.d 0 3) (by simp) with h297 | h297
                          · rcases p293_3 (m.d 1 3) (by simp) with h298 | h298
                            · rcases p293_3 (m.d 2 3) (by simp) with h299 | h299
                              · linarith only [h284, h299, hlam]
                              · linarith only [h290, h299, hlam]
                            · linarith only [h288, h298, hlam]
                          · linarith only [h297, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          rcases p293_3 (m.d 0 3) (by simp) with h304 | h304
                          · rcases p293_3 (m.d 1 3) (by simp) with h305 | h305
                            · rcases p293_3 (m.d 2 3) (by simp) with h306 | h306
                              · linarith only [h284, h306, hlam]
                              · linarith only [h291, h306, hlam]
                            · linarith only [h289, h305, hlam]
                          · linarith only [h304, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h282, h287, hc12, hlam, hphi, p293_1, u1ehi0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h287, h290, h292, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p293_1, u3ehi4]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          rcases p293_3 (m.d 0 3) (by simp) with h314 | h314
                          · linarith only [h282, h314, hlam]
                          · linarith only [h285, h314, hlam]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          rcases p293_3 (m.d 0 3) (by simp) with h317 | h317
                          · linarith only [h282, h317, hlam]
                          · linarith only [h286, h317, hlam]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h284, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h287, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h284, h292, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p293_1, u3ehi4]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h0, h284, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p293_1, u3ehi4]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h285, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h288, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h290, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hc34, hlam, hphi, p293_1, u3ehi4]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h286, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h289, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h291, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [h292, hlam, p293_0]
                        · have p293_0 := h293c.1
                          have p293_1 := h293c.2.1
                          have p293_2 := h293c.2.2.1
                          have p293_3 := h293c.2.2.2
                          linarith only [hlam, p293_0]
                      · rcases h3bigk with h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c | h335c
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h282, hlam, p335_1]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h291, h292, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p335_1, u3ehi3]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          rcases p335_3 (m.d 0 3) (by simp) with h339 | h339
                          · rcases p335_3 (m.d 1 3) (by simp) with h340 | h340
                            · rcases p335_3 (m.d 2 3) (by simp) with h341 | h341
                              · linarith only [h284, h341, hlam]
                              · linarith only [h290, h341, hlam]
                            · linarith only [h288, h340, hlam]
                          · linarith only [h339, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          rcases p335_3 (m.d 0 3) (by simp) with h346 | h346
                          · rcases p335_3 (m.d 1 3) (by simp) with h347 | h347
                            · rcases p335_3 (m.d 2 3) (by simp) with h348 | h348
                              · linarith only [h284, h348, hlam]
                              · linarith only [h291, h348, hlam]
                            · linarith only [h289, h347, hlam]
                          · linarith only [h346, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h282, h287, hc12, hlam, hphi, p335_1, u1ehi0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h287, h291, h292, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p335_1, u3ehi3]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          rcases p335_3 (m.d 0 3) (by simp) with h356 | h356
                          · linarith only [h282, h356, hlam]
                          · linarith only [h285, h356, hlam]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          rcases p335_3 (m.d 0 3) (by simp) with h359 | h359
                          · linarith only [h282, h359, hlam]
                          · linarith only [h286, h359, hlam]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h284, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h287, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h284, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p335_1, u3ehi3]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h0, h284, h292, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p335_1, u3ehi3]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h285, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h288, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h290, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h292, hlam, p335_1]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h286, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h289, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [h291, hlam, p335_0]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hc35, hlam, hphi, p335_1, u3ehi3]
                        · have p335_0 := h335c.1
                          have p335_1 := h335c.2.1
                          have p335_2 := h335c.2.2.1
                          have p335_3 := h335c.2.2.2
                          linarith only [hlam, p335_0]
                    · linarith only [h282, h286, h287, h290, h291, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h378 | h378
                    · linarith only [h290, h378, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h380 | h380
                      · rcases h3bigk with h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c | h381c
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h282, hlam, p381_1]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          rcases p381_3 (m.d 0 3) (by simp) with h384 | h384
                          · rcases p381_3 (m.d 1 3) (by simp) with h385 | h385
                            · rcases p381_3 (m.d 2 3) (by simp) with h386 | h386
                              · linarith only [h284, h386, hlam]
                              · rcases p381_3 (m.d 3 4) (by simp) with h388 | h388
                                · linarith only [h285, h388, hlam]
                                · linarith only [h290, h388, hlam]
                            · linarith only [h287, h385, hlam]
                          · linarith only [h284, h384, hlam]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h282, h287, h378, h380, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p381_1, u3ehi2]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h282, h287, h378, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p381_1, u3ehi2]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h282, h287, hc12, hlam, hphi, p381_1, u1ehi0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          rcases p381_3 (m.d 0 3) (by simp) with h397 | h397
                          · linarith only [h282, h397, hlam]
                          · linarith only [h284, h397, hlam]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h287, h378, h380, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p381_1, u3ehi2]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h287, h378, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p381_1, u3ehi2]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h284, hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h287, hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h290, hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h378, hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h285, hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h288, hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h285, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p381_1, u3ehi2]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h282, h285, h287, h378, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p381_1, u3ehi2]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h286, hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h289, hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [hc35, hlam, hphi, p381_1, u3ehi2]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [h380, hlam, p381_0]
                        · have p381_0 := h381c.1
                          have p381_1 := h381c.2.1
                          have p381_2 := h381c.2.2.1
                          have p381_3 := h381c.2.2.2
                          linarith only [hlam, p381_0]
                      · linarith only [h290, h380, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h282, h286, h289, hlam]
              · linarith only [h282, h286, h288, hc34, hlam, hphi, u3ehi4]
            · linarith only [h0, h287, hc23, hlam, hphi, ht12, u1ehi0]
          · linarith only [h285, h286, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h422 | h422
          · linarith only [h285, h422, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h424 | h424
            · rcases m.htr 1 3 4 (by decide) (by decide) with h425 | h425
              · linarith only [h282, h285, h424, h425, hc12, hlam, hphi, u1ehi0]
              · linarith only [h282, h425, hc34, hlam, hphi, ht12, ht23, u1ehi0]
            · linarith only [h284, h422, h424, hc35, hlam, hphi, ht12, ht23, u1ehi1]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h429 | h429
        · rcases m.htr 0 3 5 (by decide) (by decide) with h430 | h430
          · rcases m.htr 1 2 3 (by decide) (by decide) with h431 | h431
            · linarith only [h0, h284, h431, hc12, hlam, hphi, u1ehi0]
            · linarith only [h0, h431, hc23, hlam, hphi, ht12, u1ehi0]
          · linarith only [h429, h430, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h435 | h435
          · linarith only [h429, h435, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
            · linarith only [h0, h284, h437, hc12, hlam, hphi, u1ehi0]
            · linarith only [h0, h437, hc23, hlam, hphi, ht12, u1ehi0]

theorem r1l7_20_11_13_14_M_IR_L_I_L_R_L_0 (m : N7Model)
    (hb0 : CMSig2_7_M_IR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0ehi := hb0.2.1
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h4elo := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · linarith only [h0, h11, h13, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h10, h12, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h10, h11, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h10, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · linarith only [h0, h6, h7, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h7, h8, hlam, hphi, ht34, u3ehi2, u4elo2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h23 | h23
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h25 | h25
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                            · linarith only [h0, h22, h26, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · linarith only [h22, h24, h25, h26, h7, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo1]
                          · linarith only [h23, h25, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h23, h24, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h23, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h33 | h33
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h34 | h34
                          · linarith only [h21, h22, h34, hlam]
                          · linarith only [h32, h34, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h32, h33, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h32, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
                        · linarith only [h21, h39, h41, h5, hlam, hphi, ht34, u3ehi4, u4elo0]
                        · linarith only [h40, h41, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h40, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h45 | h45
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h46 | h46
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h47 | h47
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h48 | h48
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h49 | h49
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h50 | h50
                                · rcases h1bigk with h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c | h51c
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    rcases p51_3 (m.d 0 1) (by simp) with h53 | h53
                                    · rcases p51_3 (m.d 1 2) (by simp) with h54 | h54
                                      · linarith only [h54, hlam, p51_0]
                                      · rcases p51_3 (m.d 1 3) (by simp) with h56 | h56
                                        · linarith only [h1, h56, hlam]
                                        · linarith only [h56, h7, hlam]
                                    · linarith only [h53, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h45, h50, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p51_1, u3ehi4]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    rcases p51_3 (m.d 0 1) (by simp) with h61 | h61
                                    · rcases p51_3 (m.d 1 2) (by simp) with h62 | h62
                                      · linarith only [h0, h62, hlam]
                                      · rcases p51_3 (m.d 1 3) (by simp) with h64 | h64
                                        · linarith only [h1, h64, hlam]
                                        · linarith only [h45, h64, hlam]
                                    · linarith only [h61, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    rcases p51_3 (m.d 0 1) (by simp) with h68 | h68
                                    · rcases p51_3 (m.d 1 2) (by simp) with h69 | h69
                                      · linarith only [h0, h69, hlam]
                                      · rcases p51_3 (m.d 1 3) (by simp) with h71 | h71
                                        · linarith only [h1, h71, hlam]
                                        · linarith only [h46, h71, hlam]
                                    · linarith only [h68, hlam, p51_0]
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
                                    linarith only [h7, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h21, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h39, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h1, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    rcases p51_3 (m.d 0 1) (by simp) with h81 | h81
                                    · rcases p51_3 (m.d 1 2) (by simp) with h82 | h82
                                      · linarith only [h7, h82, hlam]
                                      · rcases p51_3 (m.d 1 3) (by simp) with h84 | h84
                                        · rcases p51_3 (m.d 1 4) (by simp) with h85 | h85
                                          · linarith only [h45, h85, hlam]
                                          · linarith only [h21, h85, hlam]
                                        · linarith only [h7, h84, hlam]
                                    · linarith only [h0, h81, hlam]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h1, h46, h47, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p51_1, u3ehi4]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h0, h4, h46, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p51_1, u3ehi4]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h2, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht23, ht34, p51_1, u4elo1]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h45, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h21, h46, h5, hlam, hphi, ht34, p51_1, u3ehi4, u4elo0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h3, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h39, h49, h5, hc12, hlam, hphi, ht23, ht34, p51_1, u4elo0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h46, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [h47, hlam, p51_0]
                                  · have p51_0 := h51c.1
                                    have p51_1 := h51c.2.1
                                    have p51_2 := h51c.2.2.1
                                    have p51_3 := h51c.2.2.2
                                    linarith only [hlam, p51_0]
                                · linarith only [h50, hlam, hphi, ht34, u3ehi3, u4elo4]
                              · linarith only [h21, h47, h49, hlam]
                            · linarith only [h45, h48, h7, hc35, hlam, hphi, u3ehi3]
                          · linarith only [h45, h47, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h45, h46, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h45, hlam, hphi, ht34, u3ehi1, u4elo3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h109 | h109
                · rcases m.htr 1 2 4 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                    · linarith only [h111, h6, hc12, hlam, hphi, ht01, u0ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h113 | h113
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                        · linarith only [h109, h111, h114, hlam]
                        · linarith only [h113, h114, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h113, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · linarith only [h109, h110, hlam, hphi, ht34, u3ehi2, u4elo2]
                · linarith only [h109, h4, h6, hc12, hc25, hlam, hphi]
            · linarith only [h4, h5, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h121 | h121
            · rcases m.htr 0 2 5 (by decide) (by decide) with h122 | h122
              · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                · linarith only [h121, h123, h4, hc12, hlam, hphi, ht01, u0ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h126 | h126
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h128 | h128
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h130 | h130
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h131 | h131
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h132 | h132
                                · rcases h1bigk with h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c | h133c
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h125, h130, h131, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1, u3ehi4]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h123, h125, h130, h131, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1, u3ehi4]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    rcases p133_3 (m.d 0 1) (by simp) with h137 | h137
                                    · rcases p133_3 (m.d 1 2) (by simp) with h138 | h138
                                      · linarith only [h0, h138, hlam]
                                      · linarith only [h125, h138, hlam]
                                    · linarith only [h137, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    rcases p133_3 (m.d 0 1) (by simp) with h142 | h142
                                    · rcases p133_3 (m.d 1 2) (by simp) with h143 | h143
                                      · linarith only [h0, h143, hlam]
                                      · linarith only [h126, h143, hlam]
                                    · linarith only [h142, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h0, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h123, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h0, h126, h129, h130, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p133_1, u3ehi4]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h0, h126, h130, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p133_1, u3ehi4]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h1, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h1, h125, h130, h131, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1, u3ehi4]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h1, h126, h129, h130, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1, u3ehi4]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h1, h126, h130, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p133_1, u3ehi4]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h2, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h125, hlam, p133_1]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h127, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h126, h130, hlam, hphi, ht34, p133_1, u3ehi4, u4elo1]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h3, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h126, hlam, p133_1]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h128, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [h129, hlam, p133_0]
                                  · have p133_0 := h133c.1
                                    have p133_1 := h133c.2.1
                                    have p133_2 := h133c.2.2.1
                                    have p133_3 := h133c.2.2.2
                                    linarith only [hlam, p133_0]
                                · linarith only [h125, h131, h132, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h129, h131, h2, hc24, hlam, hphi, u4elo0]
                            · linarith only [h130, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                          · linarith only [h127, h129, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h127, h128, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h127, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · linarith only [h122, h126, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h121, h125, h4, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h175 | h175
                · linarith only [h175, h4, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h177 | h177
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h178 | h178
                    · linarith only [h0, h122, h178, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h180 | h180
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h181 | h181
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h182 | h182
                          · linarith only [h177, h178, h182, hlam]
                          · linarith only [h180, h182, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h180, h181, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h180, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · linarith only [h121, h177, h4, hc12, hc23, hlam, hphi]
            · linarith only [h121, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h189 | h189
          · rcases m.htr 0 2 4 (by decide) (by decide) with h190 | h190
            · rcases m.htr 0 2 5 (by decide) (by decide) with h191 | h191
              · linarith only [h0, h191, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
                · linarith only [h0, h193, h3, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h189, h191, h193, hc12, hc25, hlam, hphi]
            · linarith only [h189, h190, hlam, hphi, ht34, u3ehi2, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h197 | h197
            · rcases m.htr 0 2 5 (by decide) (by decide) with h198 | h198
              · linarith only [h0, h198, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h200 | h200
                · linarith only [h189, h200, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h203 | h203
                    · linarith only [h1, h197, h198, h200, h203, hc01, hlam, hphi, u0ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h205 | h205
                      · linarith only [h1, h203, h205, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h205, hlam, hphi, ht34, u3ehi1, u4elo3]
                  · linarith only [h189, h197, h202, hc12, hc23, hlam, hphi]
            · linarith only [h197, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
      · linarith only [h1, h2, hlam, hphi, ht34, u3ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h211 | h211
      · rcases m.htr 0 1 5 (by decide) (by decide) with h212 | h212
        · rcases m.htr 0 2 3 (by decide) (by decide) with h213 | h213
          · linarith only [h0, h1, h213, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h215 | h215
            · rcases m.htr 0 2 5 (by decide) (by decide) with h216 | h216
              · rcases m.htr 1 2 3 (by decide) (by decide) with h217 | h217
                · linarith only [h213, h217, hc12, hlam, hphi, ht01, u0ehi1]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h219 | h219
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h220 | h220
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h222 | h222
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h223 | h223
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h224 | h224
                            · linarith only [h0, h1, h220, h224, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · linarith only [h0, h1, h217, h220, h222, h223, h224, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h221, h223, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h0, h1, h219, h221, h222, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1, h221, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h216, h217, h220, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h215, h217, h219, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h232 | h232
                · linarith only [h0, h1, h232, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h235 | h235
                    · linarith only [h0, h1, h215, h216, h232, h235, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h237 | h237
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h238 | h238
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h239 | h239
                          · linarith only [h234, h235, h239, hlam]
                          · linarith only [h237, h239, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h1, h238, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h1, h212, h235, h237, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h215, h216, h234, hc12, hc25, hlam, hphi]
            · linarith only [h215, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h246 | h246
          · linarith only [h0, h1, h246, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h248 | h248
            · rcases m.htr 0 2 5 (by decide) (by decide) with h249 | h249
              · linarith only [h0, h212, h249, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h251 | h251
                · linarith only [h246, h248, h251, hc12, hlam, hphi, ht01, u0ehi3]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h253 | h253
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h254 | h254
                    · linarith only [h0, h248, h249, h254, hc01, hlam, hphi, u0ehi3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h256 | h256
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h257 | h257
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h258 | h258
                          · linarith only [h0, h212, h258, hc12, hlam, hphi, ht23, ht34, u4elo1]
                          · linarith only [h256, h258, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h0, h1, h253, h257, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h253, h256, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h248, h251, h253, hc12, hc23, hlam, hphi]
            · linarith only [h248, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
      · linarith only [h211, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h266 | h266
    · rcases m.htr 0 1 4 (by decide) (by decide) with h267 | h267
      · rcases m.htr 0 1 5 (by decide) (by decide) with h268 | h268
        · rcases m.htr 0 2 3 (by decide) (by decide) with h269 | h269
          · rcases m.htr 0 2 4 (by decide) (by decide) with h270 | h270
            · rcases m.htr 0 2 5 (by decide) (by decide) with h271 | h271
              · rcases m.htr 1 2 3 (by decide) (by decide) with h272 | h272
                · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h274 | h274
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h275 | h275
                      · linarith only [h0, h266, h275, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h275, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · linarith only [h0, h274, hc25, hlam, hphi, ht01, ht12, u0ehi0]
                  · linarith only [h0, h273, hc24, hlam, hphi, ht01, ht12, u0ehi0]
                · linarith only [h0, h272, hc23, hlam, hphi, ht01, ht12, u0ehi0]
              · linarith only [h0, h268, h271, hlam]
            · linarith only [h0, h267, h270, hc14, hlam, hphi, u4elo2]
          · linarith only [h0, h266, h269, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h284 | h284
          · rcases m.htr 0 2 4 (by decide) (by decide) with h285 | h285
            · rcases m.htr 0 2 5 (by decide) (by decide) with h286 | h286
              · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h289 | h289
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h290 | h290
                      · linarith only [h266, h268, h289, h290, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h290, hlam, hphi, ht34, u3ehi1, u4elo3]
                    · linarith only [h0, h286, h289, hc02, hlam, hphi, u0ehi0]
                  · linarith only [h0, h288, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
                · linarith only [h0, h266, h287, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h296 | h296
                · rcases m.htr 1 2 4 (by decide) (by decide) with h297 | h297
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h298 | h298
                    · linarith only [h0, h266, h286, h296, h298, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h266, h296, h298, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h266, h296, h297, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h266, h296, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h285, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
          · linarith only [h0, h266, h284, hlam]
      · linarith only [h266, h267, hlam, hphi, ht34, u3ehi1, u4elo1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h306 | h306
      · rcases m.htr 0 1 5 (by decide) (by decide) with h307 | h307
        · rcases m.htr 0 2 3 (by decide) (by decide) with h308 | h308
          · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
            · rcases m.htr 0 2 5 (by decide) (by decide) with h310 | h310
              · rcases m.htr 1 2 3 (by decide) (by decide) with h311 | h311
                · rcases m.htr 1 2 4 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h313 | h313
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h314 | h314
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h315 | h315
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h316 | h316
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h317 | h317
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h318 | h318
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h319 | h319
                                · rcases h1bigk with h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c | h320c
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h0, hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h266, hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h266, h311, h312, h318, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p320_1]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h266, h311, h315, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p320_1, u3ehi4]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p320_1, u0ehi0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h266, h307, hc12, hlam, hphi, ht01, p320_1, u0ehi4]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    rcases p320_3 (m.d 0 1) (by simp) with h329 | h329
                                    · linarith only [h0, h329, hlam]
                                    · linarith only [h306, h329, hlam]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    rcases p320_3 (m.d 0 1) (by simp) with h332 | h332
                                    · linarith only [h0, h332, hlam]
                                    · linarith only [h307, h332, hlam]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h306, h313, h316, h317, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p320_1, u3ehi4]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h311, hlam, p320_1]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    rcases p320_3 (m.d 0 1) (by simp) with h338 | h338
                                    · linarith only [h266, h338, hlam]
                                    · linarith only [h306, h338, hlam]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    rcases p320_3 (m.d 0 1) (by simp) with h341 | h341
                                    · linarith only [h266, h341, hlam]
                                    · linarith only [h307, h341, hlam]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h306, hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h312, hlam, p320_1]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h314, hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h306, h313, h317, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p320_1, u3ehi4]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h307, hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h313, hlam, p320_1]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h315, hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [h316, hlam, p320_0]
                                  · have p320_0 := h320c.1
                                    have p320_1 := h320c.2.1
                                    have p320_2 := h320c.2.2.1
                                    have p320_3 := h320c.2.2.2
                                    linarith only [hlam, p320_0]
                                · linarith only [h319, hlam, hphi, ht34, u3ehi3, u4elo4]
                              · linarith only [h266, h306, h311, h316, h318, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h266, h307, h311, h315, h317, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h314, h316, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h266, h315, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                      · linarith only [h266, h306, h314, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · linarith only [h266, h306, h311, h313, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h266, h306, h311, h312, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                · linarith only [h0, h306, h308, h311, hc02, hlam, hphi, u0ehi3]
              · linarith only [h0, h307, h310, hlam]
            · linarith only [h308, h309, hlam, hphi, ht34, u3ehi0, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h365 | h365
            · rcases m.htr 0 2 5 (by decide) (by decide) with h366 | h366
              · rcases m.htr 1 2 3 (by decide) (by decide) with h367 | h367
                · linarith only [h0, h307, h308, h367, hc12, hlam, hphi, ht01, u0ehi4]
                · linarith only [h0, h307, h367, hc23, hlam, hphi, ht01, ht12, u0ehi4]
              · linarith only [h0, h307, h366, hlam]
            · linarith only [h0, h307, h365, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi4, u4elo2]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h372 | h372
          · rcases m.htr 0 2 4 (by decide) (by decide) with h373 | h373
            · rcases m.htr 0 2 5 (by decide) (by decide) with h374 | h374
              · rcases m.htr 1 2 3 (by decide) (by decide) with h375 | h375
                · rcases m.htr 1 2 4 (by decide) (by decide) with h376 | h376
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h378 | h378
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h379 | h379
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h380 | h380
                          · linarith only [h306, h307, h380, hlam]
                          · linarith only [h378, h380, hlam, hphi, ht34, u3ehi3, u4elo4]
                        · linarith only [h266, h306, h378, h379, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h266, h378, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi0]
                    · linarith only [h266, h306, h374, h375, h377, hc02, hlam, hphi, u0ehi3]
                  · linarith only [h0, h376, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
                · linarith only [h0, h306, h372, h375, hc02, hlam, hphi, u0ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h388 | h388
                · rcases m.htr 1 2 4 (by decide) (by decide) with h389 | h389
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h390 | h390
                    · linarith only [h372, h374, h390, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h306, h390, hc25, hlam, hphi, ht01, ht12, u0ehi3]
                  · linarith only [h266, h306, h388, h389, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                · linarith only [h0, h306, h372, h388, hc02, hlam, hphi, u0ehi3]
            · linarith only [h373, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi1, u4elo2]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h396 | h396
            · rcases m.htr 0 2 5 (by decide) (by decide) with h397 | h397
              · rcases m.htr 1 2 3 (by decide) (by decide) with h398 | h398
                · linarith only [h306, h307, h372, h397, h398, hc12, hlam, hphi, ht01, u0ehi3]
                · linarith only [h0, h306, h398, hc23, hlam, hphi, ht01, ht12, u0ehi3]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h401 | h401
                · linarith only [h372, h401, hc12, hlam, hphi, ht01, u0ehi1]
                · linarith only [h0, h306, h401, hc23, hlam, hphi, ht01, ht12, u0ehi3]
            · linarith only [h0, h306, h396, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3, u4elo2]
      · linarith only [h306, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi0, u4elo1]

end R2N4
