import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_12_13_15_H_R_L_R_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h14 | h14
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h15 | h15
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h16 | h16
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h18 | h18
                                      · linarith only [h0, h15, h18, h9, hc01, hc45, hlam, hphi, ht0b, ht5b]
                                      · linarith only [h0, h15, h17, h18, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                    · linarith only [h0, h12, h14, h17, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h0, h13, h16, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h12, h15, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h25 | h25
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                                    · linarith only [h0, h14, h24, h26, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h28 | h28
                                      · linarith only [h10, h14, h28, hc34, hlam, hphi, ht23, u2ehi3]
                                      · rcases h3bigk with h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c | h30c
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 3) (by simp) with h32 | h32
                                          · rcases p30_3 (m.d 1 3) (by simp) with h33 | h33
                                            · linarith only [h1, h33, hlam]
                                            · rcases p30_3 (m.d 2 3) (by simp) with h35 | h35
                                              · linarith only [h35, h4, hlam]
                                              · rcases p30_3 (m.d 3 4) (by simp) with h37 | h37
                                                · linarith only [h37, h6, hlam]
                                                · rcases p30_3 (m.d 3 5) (by simp) with h39 | h39
                                                  · linarith only [h39, h7, hlam]
                                                  · rcases h3emax with h41 | h41 | h41 | h41 | h41
                                                    · linarith only [h41, hc13, hlam, p30_1]
                                                    · linarith only [h25, h26, h41, h9, hlam, ht23, u2ehi3]
                                                    · linarith only [h25, h26, h41, hlam, ht23, u2ehi3]
                                                    · rcases h5bigk with h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c | h45c
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        rcases p45_3 (m.d 0 5) (by simp) with h47 | h47
                                                        · rcases p45_3 (m.d 1 5) (by simp) with h48 | h48
                                                          · linarith only [h3, h48, hlam]
                                                          · rcases p45_3 (m.d 2 5) (by simp) with h50 | h50
                                                            · linarith only [h11, h50, hlam, p45_1]
                                                            · rcases p45_3 (m.d 3 5) (by simp) with h52 | h52
                                                              · linarith only [h52, h7, hlam]
                                                              · rcases p45_3 (m.d 4 5) (by simp) with h54 | h54
                                                                · linarith only [h54, h8, hlam]
                                                                · linarith only [h14, h54, hlam]
                                                        · linarith only [h3, h47, hlam]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        rcases p45_3 (m.d 0 5) (by simp) with h58 | h58
                                                        · rcases p45_3 (m.d 1 5) (by simp) with h59 | h59
                                                          · linarith only [h3, h59, hlam]
                                                          · linarith only [h11, h59, hlam]
                                                        · linarith only [h58, hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        rcases p45_3 (m.d 0 5) (by simp) with h63 | h63
                                                        · rcases p45_3 (m.d 1 5) (by simp) with h64 | h64
                                                          · linarith only [h3, h64, hlam]
                                                          · linarith only [h13, h64, hlam]
                                                        · linarith only [h63, h7, hlam]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h0, h10, h14, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p45_1, u2ehi3]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h3, hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h26, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p45_1, u2ehi3]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h0, h13, h28, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1, p45_1]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h14, hlam, p45_1]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h25, hc23, hlam, hphi, ht01, ht12, p45_1, u0ehi4]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h11, hlam, p45_1]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h0, h25, h28, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1, p45_1]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h26, hlam, p45_1]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h7, hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h13, hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h25, hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h28, hlam, p45_1]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h8, hlam, p45_0]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h0, h10, h14, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p45_1, u2ehi3]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [h0, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p45_1, u2ehi4]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        rcases p45_3 (m.d 0 5) (by simp) with h87 | h87
                                                        · rcases p45_3 (m.d 1 5) (by simp) with h88 | h88
                                                          · linarith only [h14, h88, hlam]
                                                          · linarith only [h13, h88, hlam]
                                                        · linarith only [h7, h87, hlam]
                                                      · have p45_0 := h45c.1
                                                        have p45_1 := h45c.2.1
                                                        have p45_2 := h45c.2.2.1
                                                        have p45_3 := h45c.2.2.2
                                                        linarith only [hlam, p45_0]
                                                    · rcases h5bigk with h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c | h93c
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        rcases p93_3 (m.d 0 5) (by simp) with h95 | h95
                                                        · rcases p93_3 (m.d 1 5) (by simp) with h96 | h96
                                                          · linarith only [h3, h96, hlam]
                                                          · rcases p93_3 (m.d 2 5) (by simp) with h98 | h98
                                                            · linarith only [h10, h14, h98, hc25, hlam, hphi, p93_1, u2ehi3]
                                                            · rcases p93_3 (m.d 3 5) (by simp) with h100 | h100
                                                              · linarith only [h100, h7, hlam]
                                                              · rcases p93_3 (m.d 4 5) (by simp) with h102 | h102
                                                                · linarith only [h102, h8, hlam]
                                                                · linarith only [h102, h14, hlam]
                                                        · linarith only [h3, h95, hlam]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        rcases p93_3 (m.d 0 5) (by simp) with h106 | h106
                                                        · rcases p93_3 (m.d 1 5) (by simp) with h107 | h107
                                                          · linarith only [h107, h3, hlam]
                                                          · linarith only [h107, h11, hlam]
                                                        · linarith only [h106, hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        rcases p93_3 (m.d 0 5) (by simp) with h111 | h111
                                                        · rcases p93_3 (m.d 1 5) (by simp) with h112 | h112
                                                          · linarith only [h112, h3, hlam]
                                                          · linarith only [h112, h13, hlam]
                                                        · linarith only [h111, h7, hlam]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h0, h10, h14, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p93_1, u2ehi3]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h3, hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p93_1, u2ehi4]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h0, h13, h28, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1, p93_1]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h14, hlam, p93_1]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [hc25, hlam, hphi, ht01, ht12, p93_1, u0ehi4]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h11, hlam, p93_1]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h0, h11, h13, h28, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1, p93_1]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h26, hlam, p93_1]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h7, hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h13, hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h25, hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h28, hlam, p93_1]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h8, hlam, p93_0]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h0, h10, h14, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p93_1, u2ehi3]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [h0, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p93_1, u2ehi4]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        rcases p93_3 (m.d 0 5) (by simp) with h135 | h135
                                                        · rcases p93_3 (m.d 1 5) (by simp) with h136 | h136
                                                          · linarith only [h136, h14, hlam]
                                                          · linarith only [h13, h136, hlam]
                                                        · linarith only [h135, h7, hlam]
                                                      · have p93_0 := h93c.1
                                                        have p93_1 := h93c.2.1
                                                        have p93_2 := h93c.2.2.1
                                                        have p93_3 := h93c.2.2.2
                                                        linarith only [hlam, p93_0]
                                          · linarith only [h1, h32, hlam]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 3) (by simp) with h142 | h142
                                          · rcases p30_3 (m.d 1 3) (by simp) with h143 | h143
                                            · linarith only [h1, h143, hlam]
                                            · linarith only [h143, h9, hlam]
                                          · linarith only [h142, h4, hlam]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 3) (by simp) with h147 | h147
                                          · rcases p30_3 (m.d 1 3) (by simp) with h148 | h148
                                            · linarith only [h1, h148, hlam]
                                            · linarith only [h12, h148, hlam]
                                          · linarith only [h147, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 3) (by simp) with h152 | h152
                                          · rcases p30_3 (m.d 1 3) (by simp) with h153 | h153
                                            · linarith only [h1, h153, hlam]
                                            · linarith only [h13, h153, hlam]
                                          · linarith only [h152, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h1, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h1, h25, h28, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 3) (by simp) with h160 | h160
                                          · rcases p30_3 (m.d 1 3) (by simp) with h161 | h161
                                            · rcases p30_3 (m.d 2 3) (by simp) with h162 | h162
                                              · linarith only [h162, h9, hlam]
                                              · linarith only [h162, h24, hlam]
                                            · linarith only [h161, hlam, p30_0]
                                          · linarith only [h160, h6, hlam]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          rcases p30_3 (m.d 0 3) (by simp) with h167 | h167
                                          · rcases p30_3 (m.d 1 3) (by simp) with h168 | h168
                                            · rcases p30_3 (m.d 2 3) (by simp) with h169 | h169
                                              · linarith only [h169, h9, hlam]
                                              · linarith only [h169, h25, hlam]
                                            · linarith only [h168, hlam, p30_0]
                                          · linarith only [h167, h7, hlam]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h4, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h9, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h28, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h6, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h12, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h24, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h28, hlam, p30_1]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h7, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h13, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h25, hlam, p30_0]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [h0, h13, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p30_1]
                                        · have p30_0 := h30c.1
                                          have p30_1 := h30c.2.1
                                          have p30_2 := h30c.2.2.1
                                          have p30_3 := h30c.2.2.2
                                          linarith only [hlam, p30_0]
                                  · linarith only [h0, h13, h25, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · linarith only [h0, h12, h24, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h191 | h191
                              · linarith only [h12, h13, h191, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                                  · linarith only [h10, h12, h13, h194, hc23, hlam, hphi, u2ehi3]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
                                    · linarith only [h10, h191, h196, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
                                      · linarith only [h10, h191, h193, h198, h9, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                      · rcases h3bigk with h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          rcases p200_3 (m.d 0 3) (by simp) with h202 | h202
                                          · rcases p200_3 (m.d 1 3) (by simp) with h203 | h203
                                            · linarith only [h1, h203, hlam]
                                            · rcases p200_3 (m.d 2 3) (by simp) with h205 | h205
                                              · linarith only [h205, h4, hlam]
                                              · rcases p200_3 (m.d 3 4) (by simp) with h207 | h207
                                                · linarith only [h207, h6, hlam]
                                                · rcases p200_3 (m.d 3 5) (by simp) with h209 | h209
                                                  · linarith only [h209, h7, hlam]
                                                  · linarith only [h13, h209, hlam]
                                          · linarith only [h1, h202, hlam]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          rcases p200_3 (m.d 0 3) (by simp) with h213 | h213
                                          · rcases p200_3 (m.d 1 3) (by simp) with h214 | h214
                                            · linarith only [h1, h214, hlam]
                                            · linarith only [h214, h9, hlam]
                                          · linarith only [h213, h4, hlam]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h13, h193, h198, h6, h8, h9, hlam, p200_2]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h0, h13, h193, h4, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p200_1]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h1, hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h13, h193, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p200_1]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h0, h13, h4, h7, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p200_1]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h13, hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h4, hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h9, hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h0, h13, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p200_1]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h194, hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h6, hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h12, hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h193, hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h198, hlam, p200_1]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h7, hlam, p200_0]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h0, h10, h12, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1, u2ehi3]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1, u2ehi2]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          rcases p200_3 (m.d 0 3) (by simp) with h238 | h238
                                          · rcases p200_3 (m.d 1 3) (by simp) with h239 | h239
                                            · linarith only [h13, h239, hlam]
                                            · linarith only [h12, h239, hlam]
                                          · linarith only [h238, h6, hlam]
                                        · have p200_0 := h200c.1
                                          have p200_1 := h200c.2.1
                                          have p200_2 := h200c.2.2.1
                                          have p200_3 := h200c.2.2.2
                                          linarith only [hlam, p200_0]
                                · linarith only [h1, h12, h193, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h245 | h245
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                                · linarith only [h11, h12, h245, h247, hc23, hlam, hphi, u2ehi4]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h249 | h249
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h250 | h250
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h251 | h251
                                      · rcases h3bigk with h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c | h252c
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          rcases p252_3 (m.d 0 3) (by simp) with h254 | h254
                                          · rcases p252_3 (m.d 1 3) (by simp) with h255 | h255
                                            · linarith only [h1, h255, hlam]
                                            · rcases p252_3 (m.d 2 3) (by simp) with h257 | h257
                                              · linarith only [h257, h4, hlam]
                                              · rcases p252_3 (m.d 3 4) (by simp) with h259 | h259
                                                · linarith only [h259, h6, hlam]
                                                · linarith only [h12, h259, hlam]
                                          · linarith only [h1, h254, hlam]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          rcases p252_3 (m.d 0 3) (by simp) with h263 | h263
                                          · rcases p252_3 (m.d 1 3) (by simp) with h264 | h264
                                            · linarith only [h1, h264, hlam]
                                            · linarith only [h264, h9, hlam]
                                          · linarith only [h263, h4, hlam]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h0, h11, h12, h245, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p252_1, u2ehi4]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h12, h249, h6, h9, hlam, p252_2]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h1, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h12, h6, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p252_1]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h12, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h0, h12, h251, h4, h6, hc01, hc45, hlam, hphi, ht0b, ht5b, p252_1]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h4, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h9, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h247, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h0, h251, h9, hc01, hc45, hlam, hphi, ht0b, ht5b, p252_1]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h6, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h0, h11, h245, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p252_1, u2ehi4]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p252_1, u2ehi2]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          rcases p252_3 (m.d 0 3) (by simp) with h284 | h284
                                          · rcases p252_3 (m.d 1 3) (by simp) with h285 | h285
                                            · linarith only [h12, h285, hlam]
                                            · linarith only [h245, h285, hlam]
                                          · linarith only [h284, h7, hlam]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h7, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h245, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h249, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [h251, hlam, p252_0]
                                        · have p252_0 := h252c.1
                                          have p252_1 := h252c.2.1
                                          have p252_2 := h252c.2.2.1
                                          have p252_3 := h252c.2.2.2
                                          linarith only [hlam, p252_0]
                                      · linarith only [h0, h12, h249, h251, h4, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                    · linarith only [h2, h246, h250, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h1, h245, h249, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h12, h245, h246, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h298 | h298
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h299 | h299
                                · linarith only [h12, h299, h9, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h301 | h301
                                  · linarith only [h245, h301, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h303 | h303
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h304 | h304
                                      · rcases h3bigk with h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c | h305c
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          rcases p305_3 (m.d 0 3) (by simp) with h307 | h307
                                          · rcases p305_3 (m.d 1 3) (by simp) with h308 | h308
                                            · linarith only [h1, h308, hlam]
                                            · rcases p305_3 (m.d 2 3) (by simp) with h310 | h310
                                              · linarith only [h310, h4, hlam]
                                              · rcases p305_3 (m.d 3 4) (by simp) with h312 | h312
                                                · linarith only [h312, h6, hlam]
                                                · linarith only [h12, h312, hlam]
                                          · linarith only [h1, h307, hlam]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          rcases p305_3 (m.d 0 3) (by simp) with h316 | h316
                                          · rcases p305_3 (m.d 1 3) (by simp) with h317 | h317
                                            · linarith only [h1, h317, hlam]
                                            · linarith only [h317, h9, hlam]
                                          · linarith only [h316, h4, hlam]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h0, h245, h304, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p305_1, u2ehi2]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h0, h245, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p305_1, u2ehi2]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h1, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h245, h304, hc34, hlam, hphi, ht23, p305_1, u2ehi2]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h12, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h245, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h4, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h9, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h299, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h301, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h6, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h0, h4, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p305_1, u2ehi2]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h0, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p305_1, u2ehi2]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h0, h245, h4, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p305_1, u2ehi2]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h7, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h9, hc35, hlam, hphi, ht23, p305_1, u2ehi2]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h0, h4, h7, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p305_1, u2ehi2]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [h304, hlam, p305_0]
                                        · have p305_0 := h305c.1
                                          have p305_1 := h305c.2.1
                                          have p305_2 := h305c.2.2.1
                                          have p305_3 := h305c.2.2.2
                                          linarith only [hlam, p305_0]
                                      · linarith only [h0, h12, h304, h4, h6, h8, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · linarith only [h2, h298, h303, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h345 | h345
                                · linarith only [h12, h345, h9, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h347 | h347
                                  · linarith only [h245, h347, h9, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h349 | h349
                                    · linarith only [h12, h298, h349, h9, hc24, hlam, hphi, u2ehi2]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h351 | h351
                                      · linarith only [h12, h298, h351, h9, hc34, hlam, hphi, ht23, u2ehi2]
                                      · linarith only [h12, h351, h9, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                        · linarith only [h11, h9, hc25, hlam, hphi, u2ehi2]
                      · linarith only [h10, h9, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h356 | h356
                      · linarith only [h356, h9, hc23, hlam, hphi, u2ehi3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h358 | h358
                        · linarith only [h0, h358, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h360 | h360
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h361 | h361
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h362 | h362
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h363 | h363
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h364 | h364
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h365 | h365
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h366 | h366
                                      · rcases h3bigk with h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c | h367c
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h0, h360, h366, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p367_1]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h0, h358, h363, h365, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p367_1, u2ehi1]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          rcases p367_3 (m.d 0 3) (by simp) with h371 | h371
                                          · rcases p367_3 (m.d 1 3) (by simp) with h372 | h372
                                            · linarith only [h1, h372, hlam]
                                            · linarith only [h360, h372, hlam]
                                          · linarith only [h371, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          rcases p367_3 (m.d 0 3) (by simp) with h376 | h376
                                          · rcases p367_3 (m.d 1 3) (by simp) with h377 | h377
                                            · linarith only [h1, h377, hlam]
                                            · linarith only [h361, h377, hlam]
                                          · linarith only [h376, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h1, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h9, hlam, p367_1]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h1, h366, hc01, hc45, hlam, hphi, ht0b, ht5b, p367_1]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          rcases p367_3 (m.d 0 3) (by simp) with h385 | h385
                                          · rcases p367_3 (m.d 1 3) (by simp) with h386 | h386
                                            · rcases p367_3 (m.d 2 3) (by simp) with h387 | h387
                                              · rcases p367_3 (m.d 3 4) (by simp) with h388 | h388
                                                · linarith only [h360, h388, hlam]
                                                · linarith only [h366, h388, hlam]
                                              · linarith only [h364, h387, hlam]
                                            · linarith only [h386, hlam, p367_0]
                                          · linarith only [h385, h7, hlam]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h4, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h9, hc23, hlam, hphi, p367_1, u2ehi1]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h0, h366, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p367_1]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          rcases p367_3 (m.d 0 3) (by simp) with h398 | h398
                                          · rcases p367_3 (m.d 1 3) (by simp) with h399 | h399
                                            · linarith only [h399, h9, hlam]
                                            · linarith only [h361, h399, hlam]
                                          · linarith only [h398, h7, hlam]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h6, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h360, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h363, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h1, h360, h366, hc01, hc45, hlam, hphi, ht0b, ht5b, p367_1]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h7, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h361, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h364, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [h366, hlam, p367_0]
                                        · have p367_0 := h367c.1
                                          have p367_1 := h367c.2.1
                                          have p367_2 := h367c.2.2.1
                                          have p367_3 := h367c.2.2.2
                                          linarith only [hlam, p367_0]
                                      · rcases h3bigk with h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c | h413c
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h0, h360, h362, h366, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p413_1]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p413_1, u2ehi1]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          rcases p413_3 (m.d 0 3) (by simp) with h417 | h417
                                          · rcases p413_3 (m.d 1 3) (by simp) with h418 | h418
                                            · linarith only [h1, h418, hlam]
                                            · linarith only [h360, h418, hlam]
                                          · linarith only [h417, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          rcases p413_3 (m.d 0 3) (by simp) with h422 | h422
                                          · rcases p413_3 (m.d 1 3) (by simp) with h423 | h423
                                            · linarith only [h1, h423, hlam]
                                            · linarith only [h361, h423, hlam]
                                          · linarith only [h422, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h1, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h9, hlam, p413_1]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          rcases p413_3 (m.d 0 3) (by simp) with h430 | h430
                                          · rcases p413_3 (m.d 1 3) (by simp) with h431 | h431
                                            · rcases p413_3 (m.d 2 3) (by simp) with h432 | h432
                                              · rcases p413_3 (m.d 3 4) (by simp) with h433 | h433
                                                · linarith only [h433, hlam, p413_0]
                                                · rcases p413_3 (m.d 3 5) (by simp) with h435 | h435
                                                  · linarith only [h361, h435, hlam]
                                                  · linarith only [h366, h435, hlam]
                                              · linarith only [h363, h432, hlam]
                                            · linarith only [h431, hlam, p413_0]
                                          · linarith only [h430, h6, hlam]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          rcases p413_3 (m.d 0 3) (by simp) with h441 | h441
                                          · rcases p413_3 (m.d 1 3) (by simp) with h442 | h442
                                            · rcases p413_3 (m.d 2 3) (by simp) with h443 | h443
                                              · rcases p413_3 (m.d 3 4) (by simp) with h444 | h444
                                                · linarith only [h360, h444, hlam]
                                                · rcases p413_3 (m.d 3 5) (by simp) with h446 | h446
                                                  · linarith only [h446, hlam, p413_0]
                                                  · rcases h3emax with h448 | h448 | h448 | h448 | h448
                                                    · linarith only [h448, hlam, ht01, ht12, ht23, u0ehi2]
                                                    · linarith only [h360, h362, h366, h448, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                                    · linarith only [h448, hlam, ht23, u2ehi2]
                                                    · rcases h5bigk with h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c | h452c
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        rcases p452_3 (m.d 0 5) (by simp) with h454 | h454
                                                        · rcases p452_3 (m.d 1 5) (by simp) with h455 | h455
                                                          · linarith only [h3, h455, hlam]
                                                          · rcases p452_3 (m.d 2 5) (by simp) with h457 | h457
                                                            · linarith only [h358, h363, h365, h457, hc23, hlam, hphi, p452_1, u2ehi1]
                                                            · linarith only [h358, h457, hlam]
                                                        · linarith only [h3, h454, hlam]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h0, h358, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p452_1, u2ehi1]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        rcases p452_3 (m.d 0 5) (by simp) with h462 | h462
                                                        · rcases p452_3 (m.d 1 5) (by simp) with h463 | h463
                                                          · linarith only [h3, h463, hlam]
                                                          · linarith only [h361, h463, hlam]
                                                        · linarith only [h462, h7, hlam]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        rcases p452_3 (m.d 0 5) (by simp) with h467 | h467
                                                        · rcases p452_3 (m.d 1 5) (by simp) with h468 | h468
                                                          · linarith only [h3, h468, hlam]
                                                          · linarith only [h362, h468, hlam]
                                                        · linarith only [h467, h8, hlam]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h3, hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h358, hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        rcases p452_3 (m.d 0 5) (by simp) with h475 | h475
                                                        · rcases p452_3 (m.d 1 5) (by simp) with h476 | h476
                                                          · rcases p452_3 (m.d 2 5) (by simp) with h477 | h477
                                                            · rcases p452_3 (m.d 3 5) (by simp) with h478 | h478
                                                              · linarith only [h361, h478, hlam]
                                                              · rcases p452_3 (m.d 4 5) (by simp) with h480 | h480
                                                                · linarith only [h362, h480, hlam]
                                                                · linarith only [h366, h480, hlam]
                                                            · linarith only [h364, h477, hlam]
                                                          · linarith only [h361, h476, hlam]
                                                        · linarith only [h475, h7, hlam]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h0, h356, h362, h363, h366, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [hc25, hlam, hphi, ht01, ht12, p452_1, u0ehi4]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h358, hc25, hlam, hphi, p452_1, u2ehi1]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        rcases p452_3 (m.d 0 5) (by simp) with h490 | h490
                                                        · rcases p452_3 (m.d 1 5) (by simp) with h491 | h491
                                                          · linarith only [h358, h491, hlam]
                                                          · linarith only [h361, h491, hlam]
                                                        · linarith only [h490, h7, hlam]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h0, h363, h365, h366, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h7, hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h361, hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h364, hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h366, hlam, p452_1]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h8, hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h362, hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h365, hlam, p452_0]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [h0, h356, h362, h363, h366, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p452_1]
                                                      · have p452_0 := h452c.1
                                                        have p452_1 := h452c.2.1
                                                        have p452_2 := h452c.2.2.1
                                                        have p452_3 := h452c.2.2.2
                                                        linarith only [hlam, p452_0]
                                                    · rcases h5bigk with h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c | h506c
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        rcases p506_3 (m.d 0 5) (by simp) with h508 | h508
                                                        · rcases p506_3 (m.d 1 5) (by simp) with h509 | h509
                                                          · linarith only [h3, h509, hlam]
                                                          · rcases p506_3 (m.d 2 5) (by simp) with h511 | h511
                                                            · linarith only [h0, h358, h363, h365, h4, h511, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                                            · linarith only [h358, h511, hlam]
                                                        · linarith only [h3, h508, hlam]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h0, h358, h4, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p506_1, u2ehi1]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        rcases p506_3 (m.d 0 5) (by simp) with h516 | h516
                                                        · rcases p506_3 (m.d 1 5) (by simp) with h517 | h517
                                                          · linarith only [h3, h517, hlam]
                                                          · linarith only [h361, h517, hlam]
                                                        · linarith only [h516, h7, hlam]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        rcases p506_3 (m.d 0 5) (by simp) with h521 | h521
                                                        · rcases p506_3 (m.d 1 5) (by simp) with h522 | h522
                                                          · linarith only [h3, h522, hlam]
                                                          · linarith only [h362, h522, hlam]
                                                        · linarith only [h521, h8, hlam]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h3, hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h358, hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        rcases p506_3 (m.d 0 5) (by simp) with h529 | h529
                                                        · rcases p506_3 (m.d 1 5) (by simp) with h530 | h530
                                                          · rcases p506_3 (m.d 2 5) (by simp) with h531 | h531
                                                            · rcases p506_3 (m.d 3 5) (by simp) with h532 | h532
                                                              · linarith only [h361, h532, hlam]
                                                              · rcases p506_3 (m.d 4 5) (by simp) with h534 | h534
                                                                · linarith only [h362, h534, hlam]
                                                                · linarith only [h366, h534, hlam]
                                                            · linarith only [h364, h531, hlam]
                                                          · linarith only [h361, h530, hlam]
                                                        · linarith only [h529, h7, hlam]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h0, h356, h362, h363, h366, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p506_1]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [hc25, hlam, hphi, ht01, ht12, p506_1, u0ehi4]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h358, hc25, hlam, hphi, p506_1, u2ehi1]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        rcases p506_3 (m.d 0 5) (by simp) with h544 | h544
                                                        · rcases p506_3 (m.d 1 5) (by simp) with h545 | h545
                                                          · linarith only [h358, h545, hlam]
                                                          · linarith only [h361, h545, hlam]
                                                        · linarith only [h544, h7, hlam]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h0, h363, h365, h366, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p506_1]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h7, hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h361, hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h364, hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h366, hlam, p506_1]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h8, hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h362, hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h365, hlam, p506_0]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [h0, h356, h362, h363, h366, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p506_1]
                                                      · have p506_0 := h506c.1
                                                        have p506_1 := h506c.2.1
                                                        have p506_2 := h506c.2.2.1
                                                        have p506_3 := h506c.2.2.2
                                                        linarith only [hlam, p506_0]
                                              · linarith only [h364, h443, hlam]
                                            · linarith only [h442, hlam, p413_0]
                                          · linarith only [h441, h7, hlam]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h4, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h0, h4, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p413_1, u2ehi1]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          rcases p413_3 (m.d 0 3) (by simp) with h566 | h566
                                          · rcases p413_3 (m.d 1 3) (by simp) with h567 | h567
                                            · linarith only [h567, h9, hlam]
                                            · linarith only [h360, h567, hlam]
                                          · linarith only [h566, h6, hlam]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          rcases p413_3 (m.d 0 3) (by simp) with h571 | h571
                                          · rcases p413_3 (m.d 1 3) (by simp) with h572 | h572
                                            · linarith only [h572, h9, hlam]
                                            · linarith only [h361, h572, hlam]
                                          · linarith only [h571, h7, hlam]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h6, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h360, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h363, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h366, hlam, p413_1]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h7, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h361, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h364, hlam, p413_0]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [h1, h361, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p413_1]
                                        · have p413_0 := h413c.1
                                          have p413_1 := h413c.2.1
                                          have p413_2 := h413c.2.2.1
                                          have p413_3 := h413c.2.2.2
                                          linarith only [hlam, p413_0]
                                    · linarith only [h2, h362, h365, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                  · linarith only [h0, h364, h4, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h363, h9, hc34, hlam, hphi, ht23, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h589 | h589
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h590 | h590
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h591 | h591
                                    · linarith only [h356, h362, h589, h591, hc23, hlam, hphi, u2ehi1]
                                    · linarith only [h0, h356, h4, h591, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h361, h590, h9, hlam]
                                · linarith only [h0, h4, h589, h6, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h596 | h596
                              · linarith only [h360, h361, h596, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h598 | h598
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h599 | h599
                                  · linarith only [h0, h360, h361, h4, h599, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                                  · linarith only [h0, h4, h599, h7, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h360, h598, h9, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h603 | h603
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h604 | h604
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h605 | h605
                                · linarith only [h0, h358, h360, h4, h603, h605, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h4, h6, h605, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · linarith only [h360, h603, h604, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h609 | h609
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h610 | h610
                                · linarith only [h0, h360, h4, h610, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                · linarith only [h0, h4, h6, h610, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h613 | h613
                                · linarith only [h360, h613, h9, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h0, h4, h6, h613, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                  · linarith only [h8, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
                · linarith only [h7, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
              · linarith only [h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc24, hlam, hphi, ht01, ht12, u0ehi1]
          · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc15, hlam, hphi, ht01, u0ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, ht01, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

end R2N4
