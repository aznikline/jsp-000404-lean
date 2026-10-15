import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_14_H_R_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h11 | h11
                        · linarith only [h0, h11, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h13 | h13
                          · linarith only [h0, h11, h13, h6, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h15 | h15
                            · linarith only [h0, h11, h15, h6, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h10, h15, h6, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18 | h18
                        · linarith only [h0, h18, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                          · linarith only [h0, h18, h20, h6, h9, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h22 | h22
                            · linarith only [h0, h10, h2, h22, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h24 | h24
                              · linarith only [h10, h24, h9, hlam]
                              · rcases h2bigk with h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p26_1, u4ehi2]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h1, h10, h18, h4, h5, h9, hlam, p26_2]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  rcases p26_3 (m.d 0 2) (by simp) with h30 | h30
                                  · rcases p26_3 (m.d 1 2) (by simp) with h31 | h31
                                    · linarith only [h0, h31, hlam]
                                    · linarith only [h31, h7, hlam]
                                  · linarith only [h30, hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  rcases p26_3 (m.d 0 2) (by simp) with h35 | h35
                                  · rcases p26_3 (m.d 1 2) (by simp) with h36 | h36
                                    · linarith only [h0, h36, hlam]
                                    · linarith only [h36, h8, hlam]
                                  · linarith only [h35, hlam, p26_0]
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
                                  rcases p26_3 (m.d 0 2) (by simp) with h42 | h42
                                  · rcases p26_3 (m.d 1 2) (by simp) with h43 | h43
                                    · rcases p26_3 (m.d 2 3) (by simp) with h44 | h44
                                      · linarith only [h44, hlam, p26_0]
                                      · rcases p26_3 (m.d 2 4) (by simp) with h46 | h46
                                        · linarith only [h46, h7, hlam]
                                        · linarith only [h18, h46, hlam]
                                    · linarith only [h43, hlam, p26_0]
                                  · linarith only [h1, h42, hlam]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p26_1, u4ehi2]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h0, h22, hc01, hlam, hphi, ht0b, ht45, ht5b, p26_1, u4ehi2]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h1, hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h6, hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h18, hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h20, hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h2, hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h7, hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h22, hlam, p26_1]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h3, hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h8, hlam, p26_0]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p26_1, u4ehi2]
                                · have p26_0 := h26c.1
                                  have p26_1 := h26c.2.1
                                  have p26_2 := h26c.2.2.1
                                  have p26_3 := h26c.2.2.2
                                  linarith only [hlam, p26_0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h68 | h68
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h69 | h69
                        · linarith only [h0, h1, h68, h69, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                            · linarith only [h0, h7, h72, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h68, h7, h72, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h75 | h75
                            · linarith only [h0, h7, h75, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h1, h4, h68, h75, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h78 | h78
                        · linarith only [h0, h1, h4, h5, h6, h68, h78, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h80 | h80
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h81 | h81
                            · linarith only [h0, h2, h68, h81, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · linarith only [h78, h80, h81, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h84 | h84
                            · linarith only [h0, h2, h68, h84, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h86 | h86
                              · linarith only [h0, h1, h4, h68, h7, h86, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                              · rcases h2bigk with h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c | h88c
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h1, h4, h5, h6, h86, h9, hlam, p88_2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  rcases p88_3 (m.d 0 2) (by simp) with h92 | h92
                                  · rcases p88_3 (m.d 1 2) (by simp) with h93 | h93
                                    · linarith only [h0, h93, hlam]
                                    · linarith only [h7, h93, hlam]
                                  · linarith only [h92, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  rcases p88_3 (m.d 0 2) (by simp) with h97 | h97
                                  · rcases p88_3 (m.d 1 2) (by simp) with h98 | h98
                                    · linarith only [h0, h98, hlam]
                                    · linarith only [h8, h98, hlam]
                                  · linarith only [h97, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  rcases p88_3 (m.d 0 2) (by simp) with h104 | h104
                                  · rcases p88_3 (m.d 1 2) (by simp) with h105 | h105
                                    · rcases p88_3 (m.d 2 3) (by simp) with h106 | h106
                                      · linarith only [h106, hlam, p88_0]
                                      · rcases p88_3 (m.d 2 4) (by simp) with h108 | h108
                                        · linarith only [h108, h7, hlam]
                                        · linarith only [h108, h78, hlam]
                                    · linarith only [h105, hlam, p88_0]
                                  · linarith only [h1, h104, hlam]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, h84, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h1, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h6, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h78, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h80, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h2, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h7, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h84, hlam, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h3, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h8, hlam, p88_0]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p88_1]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p88_1, u4ehi2]
                                · have p88_0 := h88c.1
                                  have p88_1 := h88c.2.1
                                  have p88_2 := h88c.2.2.1
                                  have p88_3 := h88c.2.2.2
                                  linarith only [hlam, p88_0]
                  · linarith only [h0, h3, h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h131 | h131
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h132 | h132
                    · linarith only [h0, h132, h2, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h134 | h134
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h135 | h135
                        · linarith only [h0, h132, h135, h2, h6, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h137 | h137
                          · linarith only [h0, h1, h135, h137, h4, h6, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h139 | h139
                            · linarith only [h0, h1, h131, h135, h139, h4, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h131, h137, h139, h7, hc23, hc45, hlam, hphi, ht34]
                      · linarith only [h131, h134, h7, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                    · linarith only [h0, h143, h2, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h145 | h145
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                        · linarith only [h0, h143, h146, h2, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                          · linarith only [h0, h1, h146, h148, h4, h6, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h151 | h151
                              · rcases h2bigk with h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c | h152c
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  rcases p152_3 (m.d 0 2) (by simp) with h154 | h154
                                  · rcases p152_3 (m.d 1 2) (by simp) with h155 | h155
                                    · linarith only [h0, h155, hlam]
                                    · rcases p152_3 (m.d 2 3) (by simp) with h157 | h157
                                      · linarith only [h1, h157, hlam]
                                      · rcases p152_3 (m.d 2 4) (by simp) with h159 | h159
                                        · linarith only [h159, h2, hlam]
                                        · linarith only [h159, h7, hlam]
                                  · linarith only [h0, h154, hlam]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h1, h131, h146, h150, h4, h6, hlam, p152_2]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h0, h131, h150, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h0, h131, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h0, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h131, h148, hc23, hc35, hlam, hphi, p152_1]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h7, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h131, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h1, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h6, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h146, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h148, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h2, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h0, h2, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  rcases p152_3 (m.d 0 2) (by simp) with h178 | h178
                                  · rcases p152_3 (m.d 1 2) (by simp) with h179 | h179
                                    · linarith only [h179, h7, hlam]
                                    · linarith only [h179, h6, hlam]
                                  · linarith only [h1, h178, hlam]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h0, h1, h131, h146, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h3, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h0, h3, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p152_1]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  rcases p152_3 (m.d 0 2) (by simp) with h187 | h187
                                  · rcases p152_3 (m.d 1 2) (by simp) with h188 | h188
                                    · linarith only [h131, h188, hlam]
                                    · linarith only [h188, h6, hlam]
                                  · linarith only [h1, h187, hlam]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [h150, hlam, p152_0]
                                · have p152_0 := h152c.1
                                  have p152_1 := h152c.2.1
                                  have p152_2 := h152c.2.2.1
                                  have p152_3 := h152c.2.2.2
                                  linarith only [hlam, p152_0]
                              · linarith only [h0, h1, h146, h151, h4, h5, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h145, h150, h7, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h196 | h196
                        · linarith only [h143, h196, h6, h7, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h198 | h198
                          · linarith only [h0, h198, h2, h6, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                            · linarith only [h0, h1, h145, h196, h200, h4, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h1, h200, h4, h5, h6, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h203 | h203
                · linarith only [h0, h1, h203, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h205 | h205
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h206 | h206
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h207 | h207
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h208 | h208
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h209 | h209
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h210 | h210
                            · linarith only [h0, h1, h203, h205, h208, h210, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h203, h205, h206, h207, h210, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h205, h209, h6, hlam]
                        · linarith only [h0, h1, h205, h208, h4, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h203, h205, h207, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h216 | h216
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h217 | h217
                        · linarith only [h0, h1, h205, h206, h217, h6, hc01, hc25, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h1, h205, h216, h217, h4, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h203, h205, h216, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h221 | h221
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h222 | h222
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h223 | h223
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h224 | h224
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h225 | h225
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h226 | h226
                              · linarith only [h0, h1, h221, h226, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h1, h203, h222, h223, h226, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h203, h222, h225, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h230 | h230
                            · linarith only [h223, h224, h230, hlam]
                            · linarith only [h203, h222, h230, hlam]
                        · linarith only [h221, h223, h6, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h235 | h235
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h236 | h236
                            · linarith only [h0, h1, h222, h234, h236, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h238 | h238
                              · linarith only [h203, h221, h236, h238, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases h2bigk with h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c | h240c
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h1, h203, h236, h4, h5, hlam, p240_2]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h221, h6, hc02, hlam, hphi, ht0b, ht45, ht5b, p240_1, u4ehi3]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  rcases p240_3 (m.d 0 2) (by simp) with h244 | h244
                                  · rcases p240_3 (m.d 1 2) (by simp) with h245 | h245
                                    · linarith only [h0, h245, hlam]
                                    · rcases p240_3 (m.d 2 3) (by simp) with h247 | h247
                                      · linarith only [h1, h247, hlam]
                                      · linarith only [h234, h247, hlam]
                                  · linarith only [h244, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  rcases p240_3 (m.d 0 2) (by simp) with h251 | h251
                                  · rcases p240_3 (m.d 1 2) (by simp) with h252 | h252
                                    · linarith only [h0, h252, hlam]
                                    · rcases p240_3 (m.d 2 3) (by simp) with h254 | h254
                                      · linarith only [h1, h254, hlam]
                                      · linarith only [h235, h254, hlam]
                                  · linarith only [h251, hlam, p240_0]
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
                                  linarith only [h6, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h203, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h205, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h1, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  rcases p240_3 (m.d 0 2) (by simp) with h264 | h264
                                  · rcases p240_3 (m.d 1 2) (by simp) with h265 | h265
                                    · linarith only [h265, hlam, p240_0]
                                    · rcases p240_3 (m.d 2 3) (by simp) with h267 | h267
                                      · rcases p240_3 (m.d 2 4) (by simp) with h268 | h268
                                        · linarith only [h234, h268, hlam]
                                        · linarith only [h203, h268, hlam]
                                      · linarith only [h267, hlam, p240_0]
                                  · linarith only [h0, h264, hlam]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h203, hc12, hc23, hlam, hphi, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h0, h1, h205, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h2, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h0, h1, h236, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h234, hlam, p240_1]
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
                                  linarith only [h3, hlam, p240_0]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  rcases p240_3 (m.d 0 2) (by simp) with h282 | h282
                                  · rcases p240_3 (m.d 1 2) (by simp) with h283 | h283
                                    · linarith only [h283, hlam, p240_0]
                                    · rcases p240_3 (m.d 2 3) (by simp) with h285 | h285
                                      · rcases p240_3 (m.d 2 4) (by simp) with h286 | h286
                                        · linarith only [h236, h286, hlam]
                                        · linarith only [h203, h286, hlam]
                                      · linarith only [h285, h6, hlam]
                                  · linarith only [h0, h282, hlam]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h235, hlam, p240_1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [h0, h203, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p240_1, u4ehi1]
                                · have p240_0 := h240c.1
                                  have p240_1 := h240c.2.1
                                  have p240_2 := h240c.2.2.1
                                  have p240_3 := h240c.2.2.2
                                  linarith only [hlam, p240_0]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h294 | h294
                            · linarith only [h0, h2, h222, h294, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h296 | h296
                              · linarith only [h221, h235, h294, h296, h6, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                              · linarith only [h0, h1, h221, h235, h296, h4, h5, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h221, h234, h6, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h300 | h300
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h301 | h301
                        · linarith only [h0, h1, h221, h300, h301, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h303 | h303
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h304 | h304
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h305 | h305
                              · linarith only [h0, h1, h301, h303, h305, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h205, h300, h301, h303, h305, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                            · linarith only [h203, h300, h304, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h309 | h309
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h310 | h310
                              · rcases h2bigk with h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c | h311c
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h1, h301, h4, h6, hlam, p311_2]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  rcases p311_3 (m.d 0 2) (by simp) with h314 | h314
                                  · rcases p311_3 (m.d 1 2) (by simp) with h315 | h315
                                    · linarith only [h0, h315, hlam]
                                    · rcases p311_3 (m.d 2 3) (by simp) with h317 | h317
                                      · linarith only [h317, hlam, p311_0]
                                      · rcases p311_3 (m.d 2 4) (by simp) with h319 | h319
                                        · linarith only [h2, h319, hlam]
                                        · linarith only [h301, h319, hlam]
                                  · linarith only [h314, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h0, h203, h300, hc01, hlam, hphi, ht0b, ht45, ht5b, p311_1, u4ehi4]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  rcases p311_3 (m.d 0 2) (by simp) with h324 | h324
                                  · rcases p311_3 (m.d 1 2) (by simp) with h325 | h325
                                    · linarith only [h0, h325, hlam]
                                    · rcases p311_3 (m.d 2 3) (by simp) with h327 | h327
                                      · linarith only [h1, h327, hlam]
                                      · rcases p311_3 (m.d 2 4) (by simp) with h329 | h329
                                        · linarith only [h2, h329, hlam]
                                        · linarith only [h309, h329, hlam]
                                  · linarith only [h324, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h0, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h6, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h203, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h205, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h1, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h0, h1, h303, h310, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h301, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h303, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h2, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  rcases p311_3 (m.d 0 2) (by simp) with h344 | h344
                                  · rcases p311_3 (m.d 1 2) (by simp) with h345 | h345
                                    · linarith only [h345, hlam, p311_0]
                                    · rcases p311_3 (m.d 2 3) (by simp) with h347 | h347
                                      · linarith only [h301, h347, hlam]
                                      · linarith only [h347, h6, hlam]
                                  · linarith only [h0, h344, hlam]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h0, h2, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h0, h1, h301, h303, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h3, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  rcases p311_3 (m.d 0 2) (by simp) with h355 | h355
                                  · rcases p311_3 (m.d 1 2) (by simp) with h356 | h356
                                    · linarith only [h356, hlam, p311_0]
                                    · rcases p311_3 (m.d 2 3) (by simp) with h358 | h358
                                      · linarith only [h303, h358, hlam]
                                      · linarith only [h358, h6, hlam]
                                  · linarith only [h0, h355, hlam]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h6, hc12, hc25, hlam, hphi, p311_1]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [h309, hlam, p311_0]
                                · have p311_0 := h311c.1
                                  have p311_1 := h311c.2.1
                                  have p311_2 := h311c.2.2.1
                                  have p311_3 := h311c.2.2.2
                                  linarith only [hlam, p311_0]
                              · linarith only [h205, h300, h301, h309, h310, hlam]
                            · linarith only [h203, h300, h309, hlam]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h367 | h367
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h368 | h368
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h369 | h369
                            · linarith only [h0, h2, h300, h369, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h371 | h371
                              · linarith only [h367, h369, h371, hlam]
                              · rcases h2bigk with h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c | h373c
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h1, h203, h369, h4, h5, hlam, p373_2]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h0, h221, h367, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  rcases p373_3 (m.d 0 2) (by simp) with h377 | h377
                                  · rcases p373_3 (m.d 1 2) (by simp) with h378 | h378
                                    · linarith only [h0, h378, hlam]
                                    · rcases p373_3 (m.d 2 3) (by simp) with h380 | h380
                                      · linarith only [h1, h380, hlam]
                                      · linarith only [h367, h380, hlam]
                                  · linarith only [h377, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  rcases p373_3 (m.d 0 2) (by simp) with h384 | h384
                                  · rcases p373_3 (m.d 1 2) (by simp) with h385 | h385
                                    · linarith only [h0, h385, hlam]
                                    · rcases p373_3 (m.d 2 3) (by simp) with h387 | h387
                                      · linarith only [h1, h387, hlam]
                                      · linarith only [h368, h387, hlam]
                                  · linarith only [h384, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h0, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h6, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h203, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h205, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h1, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  rcases p373_3 (m.d 0 2) (by simp) with h397 | h397
                                  · rcases p373_3 (m.d 1 2) (by simp) with h398 | h398
                                    · linarith only [h398, hlam, p373_0]
                                    · rcases p373_3 (m.d 2 3) (by simp) with h400 | h400
                                      · rcases p373_3 (m.d 2 4) (by simp) with h401 | h401
                                        · linarith only [h367, h401, hlam]
                                        · linarith only [h203, h401, hlam]
                                      · linarith only [h400, hlam, p373_0]
                                  · linarith only [h0, h397, hlam]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h0, h1, hc01, hlam, hphi, ht0b, ht45, ht5b, p373_1, u4ehi2]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h0, h1, h205, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h2, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h0, h1, h369, h4, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h367, hlam, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h369, hlam, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h3, hlam, p373_0]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  rcases p373_3 (m.d 0 2) (by simp) with h415 | h415
                                  · rcases p373_3 (m.d 1 2) (by simp) with h416 | h416
                                    · linarith only [h416, hlam, p373_0]
                                    · rcases p373_3 (m.d 2 3) (by simp) with h418 | h418
                                      · rcases p373_3 (m.d 2 4) (by simp) with h419 | h419
                                        · linarith only [h369, h419, hlam]
                                        · linarith only [h203, h419, hlam]
                                      · linarith only [h418, h6, hlam]
                                  · linarith only [h0, h415, hlam]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h368, hlam, p373_1]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [h0, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, p373_1, u4ehi2]
                                · have p373_0 := h373c.1
                                  have p373_1 := h373c.2.1
                                  have p373_2 := h373c.2.2.1
                                  have p373_3 := h373c.2.2.2
                                  linarith only [hlam, p373_0]
                          · linarith only [h221, h367, h368, h6, hc12, hc35, hlam, hphi, ht23]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h428 | h428
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h429 | h429
                            · linarith only [h0, h2, h300, h429, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · linarith only [h367, h428, h429, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h432 | h432
                            · linarith only [h0, h2, h300, h432, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h434 | h434
                              · linarith only [h0, h1, h300, h4, h434, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                              · linarith only [h0, h1, h367, h4, h434, h5, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
          · linarith only [h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
        · linarith only [h3, hc25, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h1, h2, hc24, hlam, hphi, ht01, ht12, u0ehi2]
    · linarith only [h1, hc23, hlam, hphi, ht01, ht12, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_13_14_M_LR_L_R_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
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
  have h3ehi := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h9, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h3, h7, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · linarith only [h0, h11, h3, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14 | h14
                · linarith only [h0, h14, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16 | h16
                  · linarith only [h0, h14, h16, h3, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h18 | h18
                    · linarith only [h1, h18, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h0, h18, h3, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
              · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                · linarith only [h0, h22, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h24 | h24
                  · linarith only [h0, h22, h24, h3, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h26 | h26
                    · linarith only [h1, h26, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h28 | h28
                      · linarith only [h0, h24, h26, h28, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h30 | h30
                        · linarith only [h0, h24, h30, h4, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h21, h26, h30, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h33 | h33
                · linarith only [h0, h33, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h35 | h35
                  · linarith only [h0, h3, h33, h35, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h37 | h37
                    · linarith only [h1, h37, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h39 | h39
                      · linarith only [h0, h35, h37, h39, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h41 | h41
                        · linarith only [h0, h21, h35, h4, h41, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                          · linarith only [h0, h3, h43, h5, hlam, hphi, u0ehi7, u0elo0]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h45 | h45
                            · linarith only [h0, h39, h4, h43, h45, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h47 | h47
                              · linarith only [h0, h21, h4, h47, h5, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h49 | h49
                                · linarith only [h21, h49, h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                · linarith only [h0, h33, h4, h43, h49, h5, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h52 | h52
            · linarith only [h3, h4, h52, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h54 | h54
              · rcases m.htr 1 2 3 (by decide) (by decide) with h55 | h55
                · linarith only [h0, h55, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h3, h4, h55, hc12, hc24, hlam, hphi]
              · linarith only [h3, h4, h54, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h59 | h59
          · rcases m.htr 0 3 4 (by decide) (by decide) with h60 | h60
            · rcases m.htr 0 4 5 (by decide) (by decide) with h61 | h61
              · rcases m.htr 1 2 3 (by decide) (by decide) with h62 | h62
                · linarith only [h3, h59, h61, h62, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h64 | h64
                  · linarith only [h0, h64, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                  · linarith only [h3, h59, h64, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                · linarith only [h3, h59, h67, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                  · linarith only [h1, h67, h69, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                  · linarith only [h3, h59, h69, hc12, hc23, hlam, hphi]
            · linarith only [h3, h59, h60, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h73 | h73
            · rcases m.htr 0 4 5 (by decide) (by decide) with h74 | h74
              · rcases m.htr 1 2 3 (by decide) (by decide) with h75 | h75
                · linarith only [h3, h75, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h77 | h77
                  · linarith only [h1, h59, h75, h77, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                    · linarith only [h1, h79, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h73, h79, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
                · linarith only [h3, h82, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
                  · linarith only [h1, h59, h82, h84, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                    · linarith only [h1, h86, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                    · linarith only [h1, h73, h86, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h89 | h89
              · rcases m.htr 1 2 3 (by decide) (by decide) with h90 | h90
                · linarith only [h3, h90, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h92 | h92
                  · linarith only [h59, h92, hc12, hlam, hphi, ht01, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h94 | h94
                    · linarith only [h1, h73, h94, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h2, h94, h96, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h2, h98, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h89, h94, h98, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                · linarith only [h101, h3, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                  · linarith only [h1, h101, h103, h59, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                    · linarith only [h1, h105, h3, h73, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h107 | h107
                      · linarith only [h105, h107, h2, h3, h73, h89, hc45, hlam, hphi, ht34, u0ehi6, u0elo0, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h109 | h109
                        · linarith only [h109, h2, h3, h73, h89, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h111 | h111
                          · linarith only [h111, h3, h73, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                          · linarith only [h111, h3, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h114 | h114
        · rcases m.htr 0 2 4 (by decide) (by decide) with h115 | h115
          · linarith only [h0, h115, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h117 | h117
            · linarith only [h1, h117, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h119 | h119
              · rcases m.htr 1 2 3 (by decide) (by decide) with h120 | h120
                · linarith only [h0, h120, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · linarith only [h114, h115, h120, hc12, hc24, hlam, hphi]
              · linarith only [h0, h114, h119, h2, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h124 | h124
          · linarith only [h1, h114, h124, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h126 | h126
            · linarith only [h1, h126, h2, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h128 | h128
              · rcases m.htr 1 2 3 (by decide) (by decide) with h129 | h129
                · linarith only [h114, h129, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h131 | h131
                  · linarith only [h1, h124, h129, h131, hlam, hphi, u0ehi6, u0elo0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                    · linarith only [h1, h114, h126, h131, h133, h2, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                    · linarith only [h1, h133, h2, hc34, hlam, hphi, u3ehi1]
              · linarith only [h1, h128, h2, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h137 | h137
      · rcases m.htr 0 2 3 (by decide) (by decide) with h138 | h138
        · linarith only [h0, h1, h138, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h140 | h140
          · rcases m.htr 0 3 4 (by decide) (by decide) with h141 | h141
            · rcases m.htr 0 4 5 (by decide) (by decide) with h142 | h142
              · rcases m.htr 1 2 3 (by decide) (by decide) with h143 | h143
                · linarith only [h138, h140, h143, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h145 | h145
                  · linarith only [h0, h145, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                  · linarith only [h0, h1, h140, h143, h145, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h148 | h148
                · linarith only [h0, h148, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h150 | h150
                  · linarith only [h0, h1, h148, h150, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                  · linarith only [h0, h1, h140, h148, h150, hc12, hc23, hlam, hphi]
            · linarith only [h1, h137, h141, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h154 | h154
            · rcases m.htr 0 4 5 (by decide) (by decide) with h155 | h155
              · rcases m.htr 1 2 3 (by decide) (by decide) with h156 | h156
                · linarith only [h0, h1, h156, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h158 | h158
                  · linarith only [h0, h1, h140, h156, h158, hc02, hc23, hlam, hphi]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h161 | h161
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h162 | h162
                        · linarith only [h1, h137, h156, h162, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h1, h137, h155, h156, h158, h162, hc12, hc23, hlam, hphi]
                      · linarith only [h1, h161, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h1, h137, h155, h160, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h167 | h167
                · linarith only [h0, h167, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h169 | h169
                  · linarith only [h0, h1, h140, h167, h169, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h171 | h171
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h172 | h172
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h173 | h173
                        · linarith only [h1, h137, h155, h167, h173, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h175 | h175
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h177 | h177
                              · linarith only [h140, h155, h177, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                              · linarith only [h1, h137, h140, h167, h171, h177, hc23, hc45, hlam, hphi, ht01, ht12, ht34, u0ehi6, u3ehi3]
                            · linarith only [h167, h172, h176, hlam]
                          · linarith only [h1, h137, h167, h171, h175, hlam]
                      · linarith only [h1, h137, h171, h172, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1, h137, h169, h171, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h137, h154, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h185 | h185
        · linarith only [h0, h1, h185, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h187 | h187
          · linarith only [h0, h137, h187, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h189 | h189
            · rcases m.htr 0 4 5 (by decide) (by decide) with h190 | h190
              · rcases m.htr 1 2 3 (by decide) (by decide) with h191 | h191
                · linarith only [h0, h191, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h193 | h193
                  · linarith only [h0, h1, h187, h191, h193, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h195 | h195
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h196 | h196
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h197 | h197
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h198 | h198
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h199 | h199
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h200 | h200
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h201 | h201
                                · linarith only [h189, h201, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                · linarith only [h189, h190, h201, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi3]
                              · linarith only [h137, h189, h190, h193, h200, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h191, h196, h199, hlam]
                          · linarith only [h191, h196, h198, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h0, h137, h189, h190, h197, hlam, hphi, u0ehi6, u0elo2]
                      · linarith only [h0, h137, h195, h196, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                    · linarith only [h189, h195, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h210 | h210
                · linarith only [h185, h210, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h212 | h212
                  · linarith only [h0, h212, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h215 | h215
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h216 | h216
                        · linarith only [h0, h137, h190, h214, h216, hc13, hlam, hphi, ht01, u0ehi6]
                        · linarith only [h0, h137, h216, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                      · linarith only [h0, h1, h215, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                    · linarith only [h0, h1, h189, h214, hlam, hphi, u0ehi6, u0elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h221 | h221
              · rcases m.htr 1 2 3 (by decide) (by decide) with h222 | h222
                · linarith only [h0, h222, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h224 | h224
                  · linarith only [h0, h1, h189, h224, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h226 | h226
                    · linarith only [h0, h1, h189, h222, h226, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h226, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
                · linarith only [h0, h229, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
                  · linarith only [h0, h1, h189, h221, h231, hc45, hlam, hphi, u4ehi2]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h233 | h233
                    · linarith only [h0, h1, h189, h233, hc13, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h1, h233, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h236 | h236
    · rcases m.htr 0 1 4 (by decide) (by decide) with h237 | h237
      · rcases m.htr 0 2 3 (by decide) (by decide) with h238 | h238
        · rcases m.htr 0 2 4 (by decide) (by decide) with h239 | h239
          · rcases m.htr 0 3 4 (by decide) (by decide) with h240 | h240
            · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
              · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
                · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
                    · linarith only [h236, h244, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h240, h244, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h0, h237, h243, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h237, h242, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h249 | h249
                · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h251 | h251
                    · linarith only [h236, h251, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                    · linarith only [h240, h251, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                  · linarith only [h0, h236, h240, h250, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · linarith only [h0, h236, h240, h249, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h256 | h256
              · rcases m.htr 1 2 3 (by decide) (by decide) with h257 | h257
                · rcases m.htr 1 2 4 (by decide) (by decide) with h258 | h258
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h259 | h259
                    · linarith only [h0, h236, h240, h259, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h261 | h261
                      · linarith only [h0, h237, h259, h261, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h263 | h263
                        · linarith only [h0, h237, h263, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h256, h259, h263, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi1]
                  · linarith only [h0, h258, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h237, h256, h257, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h268 | h268
                · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h270 | h270
                    · linarith only [h236, h240, h270, hlam, hphi, u0ehi7, u0elo0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h272 | h272
                      · linarith only [h0, h237, h270, h272, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                        · linarith only [h0, h237, h256, h274, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h276 | h276
                          · linarith only [h240, h276, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
                            · linarith only [h238, h272, h278, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h280 | h280
                              · linarith only [h0, h237, h240, h256, h269, h280, hc12, hlam, hphi, ht01, u0ehi7]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h282 | h282
                                · linarith only [h240, h256, h282, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                · linarith only [h0, h237, h240, h268, h270, h282, hc12, hc45, hlam, hphi, ht01, ht34, u0ehi7, u3ehi2]
                  · linarith only [h0, h237, h269, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h236, h268, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h237, h239, hlam]
        · linarith only [h0, h236, h238, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h289 | h289
        · rcases m.htr 0 2 4 (by decide) (by decide) with h290 | h290
          · rcases m.htr 0 3 4 (by decide) (by decide) with h291 | h291
            · linarith only [h236, h237, h291, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
              · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                · rcases m.htr 1 2 4 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h296 | h296
                    · linarith only [h236, h291, h296, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                    · linarith only [h236, h237, h296, hc34, hlam, hphi, u3ehi1]
                  · linarith only [h0, h236, h290, h294, h295, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                · linarith only [h0, h236, h294, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h236, h237, h293, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h302 | h302
            · linarith only [h0, h236, h290, h302, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h304 | h304
              · rcases m.htr 1 2 3 (by decide) (by decide) with h305 | h305
                · rcases m.htr 1 2 4 (by decide) (by decide) with h306 | h306
                  · linarith only [h0, h290, h306, hc12, hlam, hphi, ht01, u0ehi5]
                  · linarith only [h0, h236, h305, h306, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h236, h305, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h0, h236, h290, h304, hc45, hlam, hphi, ht34, u3ehi1]
        · linarith only [h0, h236, h289, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h312 | h312
      · rcases m.htr 0 2 3 (by decide) (by decide) with h313 | h313
        · rcases m.htr 0 2 4 (by decide) (by decide) with h314 | h314
          · rcases m.htr 0 3 4 (by decide) (by decide) with h315 | h315
            · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
              · rcases m.htr 1 2 3 (by decide) (by decide) with h317 | h317
                · rcases m.htr 1 2 4 (by decide) (by decide) with h318 | h318
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h320 | h320
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h321 | h321
                        · linarith only [h312, h321, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                        · linarith only [h236, h312, h313, h316, h319, h321, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                      · linarith only [h236, h320, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h236, h312, h313, h315, h318, h319, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                  · linarith only [h236, h312, h317, h318, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h312, h316, h317, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h328 | h328
                · rcases m.htr 1 2 4 (by decide) (by decide) with h329 | h329
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h330 | h330
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h332 | h332
                        · linarith only [h312, h316, h332, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h334 | h334
                          · linarith only [h313, h334, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                          · linarith only [h313, h315, h334, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi2]
                      · linarith only [h236, h312, h331, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                    · linarith only [h236, h312, h329, h330, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                  · linarith only [h236, h312, h328, h329, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h312, h328, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h236, h312, h315, hlam]
          · linarith only [h236, h312, h313, h314, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h343 | h343
          · rcases m.htr 0 3 4 (by decide) (by decide) with h344 | h344
            · rcases m.htr 0 4 5 (by decide) (by decide) with h345 | h345
              · rcases m.htr 1 2 3 (by decide) (by decide) with h346 | h346
                · linarith only [h313, h343, h346, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h312, h345, h346, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h349 | h349
                · linarith only [h0, h313, h349, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h312, h349, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h312, h313, h344, hlam]
          · linarith only [h0, h312, h343, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h354 | h354
        · rcases m.htr 0 2 4 (by decide) (by decide) with h355 | h355
          · rcases m.htr 0 3 4 (by decide) (by decide) with h356 | h356
            · rcases m.htr 0 4 5 (by decide) (by decide) with h357 | h357
              · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
                · rcases m.htr 1 2 4 (by decide) (by decide) with h359 | h359
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                          · linarith only [h354, h363, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                          · linarith only [h356, h363, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                        · linarith only [h312, h357, h362, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h312, h360, h361, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h354, h356, h360, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                  · linarith only [h236, h355, h358, h359, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h358, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
                · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                        · linarith only [h357, h371, h373, h375, hc12, hlam, hphi, ht01, u0ehi8]
                        · linarith only [h312, h375, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                      · linarith only [h236, h374, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h236, h354, h356, h373, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h0, h355, h372, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h354, h371, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h382 | h382
              · rcases m.htr 1 2 3 (by decide) (by decide) with h383 | h383
                · rcases m.htr 1 2 4 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h385 | h385
                    · linarith only [h356, h383, h385, hc12, hlam, hphi, ht01, u0ehi7]
                    · linarith only [h236, h385, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h0, h355, h384, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h354, h383, hlam, hphi, u0ehi5, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
                · rcases m.htr 1 2 4 (by decide) (by decide) with h391 | h391
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h392 | h392
                    · linarith only [h236, h356, h390, h392, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h236, h392, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                  · linarith only [h0, h355, h391, hlam, hphi, u0ehi5, u0elo1]
                · linarith only [h0, h354, h390, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h397 | h397
            · linarith only [h354, h355, h397, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h399 | h399
              · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
                · rcases m.htr 1 2 4 (by decide) (by decide) with h401 | h401
                  · linarith only [h354, h355, h401, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h401, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h354, h400, hlam, hphi, u0ehi5, u0elo1]
              · linarith only [h354, h355, h399, hc45, hlam, hphi, ht34, u3ehi2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h406 | h406
          · rcases m.htr 0 3 4 (by decide) (by decide) with h407 | h407
            · rcases m.htr 0 4 5 (by decide) (by decide) with h408 | h408
              · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
                · linarith only [h354, h406, h408, h409, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h0, h409, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h412 | h412
                · linarith only [h354, h406, h412, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                · linarith only [h0, h412, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · linarith only [h354, h406, h407, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h416 | h416
            · rcases m.htr 0 4 5 (by decide) (by decide) with h417 | h417
              · rcases m.htr 1 2 3 (by decide) (by decide) with h418 | h418
                · linarith only [h0, h354, h418, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h418, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h421 | h421
                · linarith only [h0, h354, h421, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h421, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h424 | h424
              · rcases m.htr 1 2 3 (by decide) (by decide) with h425 | h425
                · linarith only [h0, h354, h425, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h425, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h428 | h428
                · linarith only [h0, h354, h428, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h428, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
