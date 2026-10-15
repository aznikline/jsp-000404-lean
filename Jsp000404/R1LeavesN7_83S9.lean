import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_15_H_R_L_I_L_I (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · linarith only [h0, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h6, hc23, hlam, hphi, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
              · linarith only [h0, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · linarith only [h9, hc23, hlam, hphi, u2ehi1]
          · linarith only [h2, h4, hc35, hlam, hphi, ht23, u2ehi2]
        · linarith only [h3, hc25, hlam, hphi, u2ehi0]
      · linarith only [h0, h2, hc23, hlam, hphi, u2ehi1]
    · linarith only [h0, h1, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h16 | h16
    · rcases m.htr 0 2 3 (by decide) (by decide) with h17 | h17
      · rcases m.htr 0 2 5 (by decide) (by decide) with h18 | h18
        · rcases m.htr 0 3 5 (by decide) (by decide) with h19 | h19
          · rcases m.htr 0 4 5 (by decide) (by decide) with h20 | h20
            · rcases m.htr 1 2 3 (by decide) (by decide) with h21 | h21
              · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                · linarith only [h0, h16, h22, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                · linarith only [h22, hc25, hlam, hphi, u2ehi1]
              · linarith only [h17, h21, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
              · rcases m.htr 1 2 5 (by decide) (by decide) with h27 | h27
                · linarith only [h0, h16, h27, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                · linarith only [h0, h27, hc25, hlam, hphi, u2ehi0]
              · linarith only [h17, h26, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
          · linarith only [h17, h19, hc35, hlam, hphi, ht23, u2ehi2]
        · linarith only [h18, hc25, hlam, hphi, u2ehi0]
      · linarith only [h17, hc23, hlam, hphi, u2ehi0]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h34 | h34
      · rcases m.htr 0 2 5 (by decide) (by decide) with h35 | h35
        · rcases m.htr 0 3 5 (by decide) (by decide) with h36 | h36
          · rcases m.htr 0 4 5 (by decide) (by decide) with h37 | h37
            · rcases m.htr 1 2 3 (by decide) (by decide) with h38 | h38
              · rcases m.htr 1 2 5 (by decide) (by decide) with h39 | h39
                · rcases m.htr 1 3 4 (by decide) (by decide) with h40 | h40
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h41 | h41
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h42 | h42
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h43 | h43
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h44 | h44
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h45 | h45
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h46 | h46
                              · rcases h3bigk with h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c | h47c
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h0, h16, h34, h40, h42, hc01, hc12, hlam, hphi, p47_1]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h0, h34, h43, h46, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p47_1]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  rcases p47_3 (m.d 0 3) (by simp) with h51 | h51
                                  · rcases p47_3 (m.d 1 3) (by simp) with h52 | h52
                                    · rcases p47_3 (m.d 2 3) (by simp) with h53 | h53
                                      · linarith only [h34, h53, hlam]
                                      · linarith only [h43, h53, hlam]
                                    · linarith only [h40, h52, hlam]
                                  · linarith only [h51, hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  rcases p47_3 (m.d 0 3) (by simp) with h58 | h58
                                  · rcases p47_3 (m.d 1 3) (by simp) with h59 | h59
                                    · rcases p47_3 (m.d 2 3) (by simp) with h60 | h60
                                      · linarith only [h34, h60, hlam]
                                      · linarith only [h44, h60, hlam]
                                    · linarith only [h41, h59, hlam]
                                  · linarith only [h58, hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h34, h43, h45, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p47_1, u2ehi4]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h38, h43, h45, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p47_1, u2ehi4]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  rcases p47_3 (m.d 0 3) (by simp) with h68 | h68
                                  · rcases p47_3 (m.d 1 3) (by simp) with h69 | h69
                                    · rcases p47_3 (m.d 2 3) (by simp) with h70 | h70
                                      · linarith only [h38, h70, hlam]
                                      · linarith only [h43, h70, hlam]
                                    · linarith only [h69, hlam, p47_0]
                                  · linarith only [h34, h43, h45, h68, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p47_1, u2ehi4]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  rcases p47_3 (m.d 0 3) (by simp) with h75 | h75
                                  · rcases p47_3 (m.d 1 3) (by simp) with h76 | h76
                                    · rcases p47_3 (m.d 2 3) (by simp) with h77 | h77
                                      · linarith only [h38, h77, hlam]
                                      · linarith only [h44, h77, hlam]
                                    · linarith only [h76, hlam, p47_0]
                                  · linarith only [h36, h75, hlam]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h34, hlam, p47_1]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h38, hlam, p47_1]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h0, h34, h46, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p47_1]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  rcases p47_3 (m.d 0 3) (by simp) with h86 | h86
                                  · rcases p47_3 (m.d 1 3) (by simp) with h87 | h87
                                    · rcases p47_3 (m.d 2 3) (by simp) with h88 | h88
                                      · rcases p47_3 (m.d 3 4) (by simp) with h89 | h89
                                        · linarith only [h43, h89, hlam]
                                        · linarith only [h46, h89, hlam]
                                      · linarith only [h88, hlam, p47_0]
                                    · linarith only [h41, h87, hlam]
                                  · linarith only [h36, h86, hlam]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h34, hc34, hlam, hphi, ht23, p47_1, u2ehi2]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h40, hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h43, hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h0, h34, h43, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p47_1]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h36, hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h41, hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h44, hlam, p47_0]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [h46, hlam, p47_1]
                                · have p47_0 := h47c.1
                                  have p47_1 := h47c.2.1
                                  have p47_2 := h47c.2.2.1
                                  have p47_3 := h47c.2.2.2
                                  linarith only [hlam, p47_0]
                              · rcases h3bigk with h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c | h105c
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h0, h34, h38, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi2]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h0, h34, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi2]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  rcases p105_3 (m.d 0 3) (by simp) with h109 | h109
                                  · rcases p105_3 (m.d 1 3) (by simp) with h110 | h110
                                    · rcases p105_3 (m.d 2 3) (by simp) with h111 | h111
                                      · linarith only [h111, h34, hlam]
                                      · linarith only [h111, h43, hlam]
                                    · linarith only [h110, h40, hlam]
                                  · linarith only [h109, hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  rcases p105_3 (m.d 0 3) (by simp) with h116 | h116
                                  · rcases p105_3 (m.d 1 3) (by simp) with h117 | h117
                                    · rcases p105_3 (m.d 2 3) (by simp) with h118 | h118
                                      · linarith only [h118, h34, hlam]
                                      · linarith only [h118, h44, hlam]
                                    · linarith only [h117, h41, hlam]
                                  · linarith only [h116, hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h34, h43, h45, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi4]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h38, h43, h45, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p105_1, u2ehi4]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  rcases p105_3 (m.d 0 3) (by simp) with h126 | h126
                                  · rcases p105_3 (m.d 1 3) (by simp) with h127 | h127
                                    · rcases p105_3 (m.d 2 3) (by simp) with h128 | h128
                                      · linarith only [h128, h38, hlam]
                                      · linarith only [h128, h43, hlam]
                                    · linarith only [h127, hlam, p105_0]
                                  · linarith only [h126, h34, h43, h45, h46, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  rcases p105_3 (m.d 0 3) (by simp) with h133 | h133
                                  · rcases p105_3 (m.d 1 3) (by simp) with h134 | h134
                                    · rcases p105_3 (m.d 2 3) (by simp) with h135 | h135
                                      · linarith only [h135, h38, hlam]
                                      · linarith only [h135, h44, hlam]
                                    · linarith only [h134, hlam, p105_0]
                                  · linarith only [h133, h36, hlam]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h34, hlam, p105_1]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h38, hlam, p105_1]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  rcases p105_3 (m.d 0 3) (by simp) with h143 | h143
                                  · rcases p105_3 (m.d 1 3) (by simp) with h144 | h144
                                    · rcases p105_3 (m.d 2 3) (by simp) with h145 | h145
                                      · rcases p105_3 (m.d 3 4) (by simp) with h146 | h146
                                        · linarith only [h146, hlam, p105_0]
                                        · rcases p105_3 (m.d 3 5) (by simp) with h148 | h148
                                          · linarith only [h148, h44, hlam]
                                          · linarith only [h148, h46, hlam]
                                      · linarith only [h145, hlam, p105_0]
                                    · linarith only [h144, h40, hlam]
                                  · linarith only [h143, h34, h43, h45, h46, hlam]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  rcases p105_3 (m.d 0 3) (by simp) with h154 | h154
                                  · rcases p105_3 (m.d 1 3) (by simp) with h155 | h155
                                    · rcases p105_3 (m.d 2 3) (by simp) with h156 | h156
                                      · rcases p105_3 (m.d 3 4) (by simp) with h157 | h157
                                        · linarith only [h157, h43, hlam]
                                        · rcases p105_3 (m.d 3 5) (by simp) with h159 | h159
                                          · linarith only [h159, hlam, p105_0]
                                          · rcases h5bigk with h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c | h161c
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [hlam, p161_0]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h16, hlam, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p161_1, u2ehi4]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              rcases p161_3 (m.d 0 5) (by simp) with h165 | h165
                                              · rcases p161_3 (m.d 1 5) (by simp) with h166 | h166
                                                · rcases p161_3 (m.d 2 5) (by simp) with h167 | h167
                                                  · linarith only [h167, h35, hlam]
                                                  · linarith only [h167, h44, hlam]
                                                · linarith only [h166, h41, hlam]
                                              · linarith only [h165, h36, hlam]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              rcases p161_3 (m.d 0 5) (by simp) with h172 | h172
                                              · rcases p161_3 (m.d 1 5) (by simp) with h173 | h173
                                                · rcases p161_3 (m.d 2 5) (by simp) with h174 | h174
                                                  · linarith only [h174, h35, hlam]
                                                  · linarith only [h174, h45, hlam]
                                                · linarith only [h173, h42, hlam]
                                              · linarith only [h172, h37, hlam]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h35, h38, h40, h42, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p161_1, u2ehi4]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [hlam, p161_0]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h38, h40, h42, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p161_1, u2ehi4]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              rcases p161_3 (m.d 0 5) (by simp) with h182 | h182
                                              · linarith only [h16, h182, hlam]
                                              · linarith only [h182, h36, hlam]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              rcases p161_3 (m.d 0 5) (by simp) with h185 | h185
                                              · linarith only [h16, h185, hlam]
                                              · linarith only [h185, h37, hlam]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h35, hlam, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h39, hlam, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [hlam, p161_0]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              rcases p161_3 (m.d 0 5) (by simp) with h191 | h191
                                              · rcases p161_3 (m.d 1 5) (by simp) with h192 | h192
                                                · rcases p161_3 (m.d 2 5) (by simp) with h193 | h193
                                                  · rcases p161_3 (m.d 3 5) (by simp) with h194 | h194
                                                    · linarith only [h194, h44, hlam]
                                                    · rcases p161_3 (m.d 4 5) (by simp) with h196 | h196
                                                      · linarith only [h196, h45, hlam]
                                                      · linarith only [h196, h46, hlam]
                                                  · linarith only [h193, h44, hlam]
                                                · linarith only [h192, h41, hlam]
                                              · linarith only [h191, h36, hlam]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h0, h34, h43, h45, h46, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h36, hlam, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h41, hlam, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h44, hlam, p161_0]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [hlam, p161_0]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h46, hlam, p161_0]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h37, hlam, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h42, hlam, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h45, hlam, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [h0, h34, h43, h45, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p161_1]
                                            · have p161_0 := h161c.1
                                              have p161_1 := h161c.2.1
                                              have p161_2 := h161c.2.2.1
                                              have p161_3 := h161c.2.2.2
                                              linarith only [hlam, p161_0]
                                      · linarith only [h156, hlam, p105_0]
                                    · linarith only [h155, h41, hlam]
                                  · linarith only [h154, h36, hlam]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h34, h43, h45, hc34, hlam, hphi, ht23, p105_1, u2ehi4]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h40, hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h43, hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h46, hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h36, hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h41, hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h44, hlam, p105_0]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [h0, h34, h44, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p105_1]
                                · have p105_0 := h105c.1
                                  have p105_1 := h105c.2.1
                                  have p105_2 := h105c.2.2.1
                                  have p105_3 := h105c.2.2.2
                                  linarith only [hlam, p105_0]
                            · linarith only [h45, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                          · linarith only [h44, hc35, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h43, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h16, h37, h42, hlam]
                    · linarith only [h0, h34, h36, h38, h41, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h38, h40, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h0, h39, hc25, hlam, hphi, u2ehi0]
              · linarith only [h0, h34, h38, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
              · rcases m.htr 1 2 5 (by decide) (by decide) with h235 | h235
                · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h237 | h237
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h238 | h238
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h239 | h239
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h240 | h240
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h241 | h241
                            · linarith only [h239, h241, h34, h35, h37, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                            · linarith only [h236, h238, h241, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h240, hc35, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h239, hc34, hlam, hphi, ht23, u2ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h246 | h246
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h247 | h247
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h248 | h248
                            · linarith only [h16, h238, h246, h248, h35, hc23, hlam, hphi, u2ehi4]
                            · linarith only [h248, hc45, hlam, hphi, ht23, ht34, u2ehi3]
                          · linarith only [h246, h247, hc35, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h246, hc34, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h234, h237, hc35, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h234, h236, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h0, h235, hc25, hlam, hphi, u2ehi0]
              · linarith only [h0, h234, h34, hlam]
          · linarith only [h34, h36, hc35, hlam, hphi, ht23, u2ehi2]
        · linarith only [h34, h35, hc25, hlam, hphi, u2ehi2]
      · linarith only [h34, hc23, hlam, hphi, u2ehi0]

theorem r1l7_22_13_15_H_R_L_R_L_I (m : N7Model)
    (hb2 : CMSig2_7_H_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
  have hc23 := m.hcor 2 3 (by decide)
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h11 | h11
                        · rcases h5bigk with h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c | h12c
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, h3, h5, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h1, h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            rcases p12_3 (m.d 0 5) (by simp) with h16 | h16
                            · rcases p12_3 (m.d 1 5) (by simp) with h17 | h17
                              · rcases p12_3 (m.d 2 5) (by simp) with h18 | h18
                                · linarith only [h0, h18, hlam]
                                · linarith only [h10, h18, hlam]
                              · linarith only [h17, h7, hlam]
                            · linarith only [h16, h2, hlam]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            rcases p12_3 (m.d 0 5) (by simp) with h23 | h23
                            · rcases p12_3 (m.d 1 5) (by simp) with h24 | h24
                              · rcases p12_3 (m.d 2 5) (by simp) with h25 | h25
                                · linarith only [h0, h25, hlam]
                                · linarith only [h11, h25, h4, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                              · linarith only [h24, h8, hlam]
                            · linarith only [h23, h3, hlam]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, h4, h6, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h4, h6, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p12_1, u2ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            rcases p12_3 (m.d 0 5) (by simp) with h33 | h33
                            · rcases p12_3 (m.d 1 5) (by simp) with h34 | h34
                              · rcases p12_3 (m.d 2 5) (by simp) with h35 | h35
                                · linarith only [h35, h5, hlam]
                                · linarith only [h10, h35, hlam]
                              · linarith only [h34, h7, hlam]
                            · linarith only [h2, h33, hlam]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            rcases p12_3 (m.d 0 5) (by simp) with h40 | h40
                            · rcases p12_3 (m.d 1 5) (by simp) with h41 | h41
                              · rcases p12_3 (m.d 2 5) (by simp) with h42 | h42
                                · linarith only [h42, h5, hlam]
                                · linarith only [h11, h4, h42, h9, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                              · linarith only [h41, h8, hlam]
                            · linarith only [h3, h40, hlam]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h5, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h0, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p12_1, u3ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            rcases p12_3 (m.d 0 5) (by simp) with h51 | h51
                            · rcases p12_3 (m.d 1 5) (by simp) with h52 | h52
                              · rcases p12_3 (m.d 2 5) (by simp) with h53 | h53
                                · rcases p12_3 (m.d 3 5) (by simp) with h54 | h54
                                  · linarith only [h10, h54, hlam]
                                  · linarith only [h11, h54, hlam]
                                · linarith only [h53, hlam, p12_0]
                              · linarith only [h52, h8, hlam]
                            · linarith only [h3, h51, hlam]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h2, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h7, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h10, hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h10, h4, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h3, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h8, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hc45, hlam, hphi, ht23, ht34, p12_1, u2ehi4]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [h11, hlam, p12_1]
                          · have p12_0 := h12c.1
                            have p12_1 := h12c.2.1
                            have p12_2 := h12c.2.2.1
                            have p12_3 := h12c.2.2.2
                            linarith only [hlam, p12_0]
                        · rcases h5bigk with h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c | h70c
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h1, h3, h5, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi4]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h1, h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi4]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            rcases p70_3 (m.d 0 5) (by simp) with h74 | h74
                            · rcases p70_3 (m.d 1 5) (by simp) with h75 | h75
                              · rcases p70_3 (m.d 2 5) (by simp) with h76 | h76
                                · linarith only [h0, h76, hlam]
                                · linarith only [h10, h76, hlam]
                              · linarith only [h7, h75, hlam]
                            · linarith only [h2, h74, hlam]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h1, h11, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p70_1, u3ehi3]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi4]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h5, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p70_1, u2ehi4]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            rcases p70_3 (m.d 0 5) (by simp) with h85 | h85
                            · rcases p70_3 (m.d 1 5) (by simp) with h86 | h86
                              · rcases p70_3 (m.d 2 5) (by simp) with h87 | h87
                                · linarith only [h5, h87, hlam]
                                · linarith only [h10, h87, hlam]
                              · linarith only [h7, h86, hlam]
                            · linarith only [h2, h85, hlam]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h11, h4, h6, h8, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p70_1, u3ehi3]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h0, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h5, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h0, h11, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p70_1, u3ehi3]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h10, h11, h4, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p70_1, u3ehi3]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h2, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h7, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h10, hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h11, hlam, p70_0]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h3, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h8, hlam, p70_1]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hc45, hlam, hphi, ht23, ht34, p70_1, u2ehi4]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [h11, h4, h6, h8, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p70_1, u3ehi3]
                          · have p70_0 := h70c.1
                            have p70_1 := h70c.2.1
                            have p70_2 := h70c.2.2.1
                            have p70_3 := h70c.2.2.2
                            linarith only [hlam, p70_0]
                      · linarith only [h10, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h9, hc34, hlam, hphi, ht23, u2ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h110 | h110
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h111 | h111
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h112 | h112
                        · linarith only [h112, h6, h8, hlam]
                        · rcases h5bigk with h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c | h114c
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [hlam, p114_0]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h1, h3, h5, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1, u2ehi4]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h1, h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1, u2ehi4]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            rcases p114_3 (m.d 0 5) (by simp) with h118 | h118
                            · rcases p114_3 (m.d 1 5) (by simp) with h119 | h119
                              · linarith only [h119, h8, hc45, hlam, hphi, ht34, p114_1, u3ehi4]
                              · linarith only [h119, h7, hlam]
                            · linarith only [h118, h2, hlam]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h6, h8, hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p114_1, u3ehi3]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h0, h7, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p114_1, u2ehi4]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [hlam, p114_0]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h1, h3, h8, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1, u2ehi4]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h1, h112, h3, h8, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p114_1, u3ehi3]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h8, hlam, p114_0]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h0, hlam, p114_1]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h5, hlam, p114_1]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [hlam, p114_0]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h0, h112, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p114_1, u3ehi3]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h5, h8, hlam, p114_1]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h2, hlam, p114_1]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h7, hlam, p114_1]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h111, hlam, p114_0]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [hlam, p114_0]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h112, hlam, p114_0]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h3, hlam, p114_1]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h1, h3, h5, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1, u2ehi4]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h1, h3, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p114_1, u2ehi4]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [h1, h112, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p114_1, u3ehi3]
                          · have p114_0 := h114c.1
                            have p114_1 := h114c.2.1
                            have p114_2 := h114c.2.2.1
                            have p114_3 := h114c.2.2.2
                            linarith only [hlam, p114_0]
                      · linarith only [h110, h111, hc35, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h110, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h6, h7, hc35, hlam, hphi, u3ehi3]
              · linarith only [h4, h6, hc34, hlam, hphi, ht23, u2ehi2]
            · linarith only [h5, hc25, hlam, hphi, u2ehi1]
          · linarith only [h4, hc23, hlam, hphi, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
          · rcases m.htr 1 2 5 (by decide) (by decide) with h151 | h151
            · rcases m.htr 1 3 4 (by decide) (by decide) with h152 | h152
              · rcases m.htr 1 3 5 (by decide) (by decide) with h153 | h153
                · rcases m.htr 1 4 5 (by decide) (by decide) with h154 | h154
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h155 | h155
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h156 | h156
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h157 | h157
                        · linarith only [h1, h157, h3, hlam]
                        · rcases h5bigk with h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c | h159c
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h154, h3, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h150, h152, h154, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p159_1, u2ehi4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h150, h152, h154, h3, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p159_1, u3ehi4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h3, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p159_1, u2ehi4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h151, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p159_1, u2ehi4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            rcases p159_3 (m.d 0 5) (by simp) with h168 | h168
                            · linarith only [h150, h152, h154, h157, h168, h3, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p159_1, u3ehi3]
                            · linarith only [h168, h2, hlam]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h3, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p159_1, u2ehi4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h151, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h157, h3, hc45, hlam, hphi, ht34, p159_1, u3ehi3]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h3, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h2, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h153, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h156, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h157, hlam, p159_0]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h0, h150, h152, h154, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p159_1, u2ehi4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h154, hlam, p159_1]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h150, h152, h154, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p159_1, u2ehi4]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [h150, h152, h154, h157, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p159_1, u3ehi3]
                          · have p159_0 := h159c.1
                            have p159_1 := h159c.2.1
                            have p159_2 := h159c.2.2.1
                            have p159_3 := h159c.2.2.2
                            linarith only [hlam, p159_0]
                      · linarith only [h156, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h155, hc34, hlam, hphi, ht23, u2ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h189 | h189
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h191 | h191
                        · linarith only [h1, h191, h3, hlam]
                        · rcases h5bigk with h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c | h193c
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h151, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p193_1, u2ehi4]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h3, hc45, hlam, hphi, ht23, ht34, p193_1, u2ehi4]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h3, hc45, hlam, hphi, ht34, p193_1, u3ehi4]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h3, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p193_1, u2ehi4]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h151, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p193_1, u2ehi4]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h154, h191, hc45, hlam, hphi, ht34, p193_1, u3ehi3]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h154, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, hlam, p193_1]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h151, hlam, p193_1]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, h191, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p193_1, u3ehi3]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h150, h190, h3, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p193_1]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h2, hlam, p193_1]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h153, hlam, p193_1]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h190, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h191, hlam, p193_0]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h0, hc45, hlam, hphi, ht23, ht34, p193_1, u2ehi4]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h151, hc45, hlam, hphi, ht23, ht34, p193_1, u2ehi4]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hc45, hlam, hphi, ht23, ht34, p193_1, u2ehi4]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [h191, hc45, hlam, hphi, ht34, p193_1, u3ehi3]
                          · have p193_0 := h193c.1
                            have p193_1 := h193c.2.1
                            have p193_2 := h193c.2.2.1
                            have p193_3 := h193c.2.2.2
                            linarith only [hlam, p193_0]
                      · linarith only [h190, hc35, hlam, hphi, ht23, u2ehi2]
                    · linarith only [h189, hc34, hlam, hphi, ht23, u2ehi2]
                · linarith only [h150, h153, hc35, hlam, hphi, ht23, u2ehi2]
              · linarith only [h1, h150, h152, h3, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h151, hc25, hlam, hphi, u2ehi1]
          · linarith only [h150, hc23, hlam, hphi, u2ehi1]
      · linarith only [h1, h2, hc35, hlam, hphi, u3ehi3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h226 | h226
      · linarith only [h1, h226, hc34, hlam, hphi, u3ehi4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h228 | h228
        · rcases m.htr 1 2 3 (by decide) (by decide) with h229 | h229
          · rcases m.htr 1 2 5 (by decide) (by decide) with h230 | h230
            · rcases m.htr 1 3 4 (by decide) (by decide) with h231 | h231
              · rcases m.htr 1 3 5 (by decide) (by decide) with h232 | h232
                · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                    · linarith only [h1, h229, h234, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h234, hc34, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h1, h228, h231, h233, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h229, h232, hc35, hlam, hphi, ht23, u2ehi2]
              · linarith only [h229, h231, hc34, hlam, hphi, ht23, u2ehi2]
            · linarith only [h230, hc25, hlam, hphi, u2ehi1]
          · linarith only [h229, hc23, hlam, hphi, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h242 | h242
          · rcases m.htr 1 2 5 (by decide) (by decide) with h243 | h243
            · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
              · rcases m.htr 1 3 5 (by decide) (by decide) with h245 | h245
                · rcases m.htr 1 4 5 (by decide) (by decide) with h246 | h246
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h247 | h247
                    · linarith only [h1, h242, h247, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · linarith only [h247, hc34, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h1, h244, h246, hc45, hlam, hphi, ht34, u3ehi0]
                · linarith only [h242, h245, hc35, hlam, hphi, ht23, u2ehi2]
              · linarith only [h242, h244, hc34, hlam, hphi, ht23, u2ehi2]
            · linarith only [h243, hc25, hlam, hphi, u2ehi1]
          · linarith only [h242, hc23, hlam, hphi, u2ehi1]
  · linarith only [h0, hc25, hlam, hphi, u2ehi0]

theorem r1l7_22_13_15_M_IR_L_0_L_I (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 4 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h10, h13, h6, hc01, hc45, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h10, h12, h13, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h12, h4, h5, hlam, hphi, ht23, u2ehi3, u3elo0]
                        · linarith only [h11, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h10, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h19 | h19
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h20 | h20
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h0, h19, h21, h6, h9, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h21, h4, h5, hlam, hphi, ht23, u2ehi3, u3elo0]
                        · linarith only [h19, h20, hlam, hphi, ht23, u2ehi3, u3elo4]
                      · linarith only [h19, hlam, hphi, ht23, u2ehi2, u3elo3]
                  · linarith only [h4, h8, hc13, hlam, hphi, u3elo0]
                · linarith only [h3, h4, h7, hlam, hphi, ht23, u2ehi1, u3elo0]
              · linarith only [h6, hlam, hphi, ht23, u2ehi1, u3elo2]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                · rcases m.htr 1 3 5 (by decide) (by decide) with h31 | h31
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h32 | h32
                    · linarith only [h2, h31, h32, h5, hlam, hphi, ht23, u2ehi3, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                          · linarith only [h2, h36, h5, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h38 | h38
                            · linarith only [h0, h2, h29, h34, h38, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases h2bigk with h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c | h40c
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, h29, h35, h38, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                rcases p40_3 (m.d 0 2) (by simp) with h43 | h43
                                · rcases p40_3 (m.d 1 2) (by simp) with h44 | h44
                                  · linarith only [h0, h44, hlam]
                                  · linarith only [h29, h44, hlam]
                                · linarith only [h43, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                rcases p40_3 (m.d 0 2) (by simp) with h48 | h48
                                · rcases p40_3 (m.d 1 2) (by simp) with h49 | h49
                                  · linarith only [h0, h49, hlam]
                                  · linarith only [h29, h35, h36, h49, hlam]
                                · linarith only [h48, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                rcases p40_3 (m.d 0 2) (by simp) with h53 | h53
                                · rcases p40_3 (m.d 1 2) (by simp) with h54 | h54
                                  · linarith only [h0, h54, hlam]
                                  · linarith only [h30, h54, hlam]
                                · linarith only [h53, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, hlam, p40_1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, h35, h36, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p40_1, u2ehi3]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p40_1, u2ehi3]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, h36, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p40_1, u2ehi3]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h1, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h29, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hc23, hlam, hphi, p40_1, u2ehi3]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h0, h29, h36, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p40_1, u2ehi3]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h2, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hc24, hlam, hphi, p40_1, u2ehi1]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h34, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h36, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h3, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h30, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [h35, hlam, p40_0]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hc25, hlam, hphi, p40_1, u2ehi3]
                              · have p40_0 := h40c.1
                                have p40_1 := h40c.2.1
                                have p40_2 := h40c.2.2.1
                                have p40_3 := h40c.2.2.2
                                linarith only [hlam, p40_0]
                        · linarith only [h34, h35, hlam, hphi, ht23, u2ehi3, u3elo4]
                      · linarith only [h34, hlam, hphi, ht23, u2ehi2, u3elo3]
                  · linarith only [h31, h4, hc13, hlam, hphi, u3elo0]
                · linarith only [h3, h30, h4, hlam, hphi, ht23, u2ehi1, u3elo0]
              · linarith only [h29, hlam, hphi, ht23, u2ehi1, u3elo2]
          · linarith only [h1, h4, hlam, hphi, ht23, u2ehi2, u3elo4]
        · linarith only [h1, h3, hc25, hlam, hphi, u2ehi2]
      · linarith only [h1, h2, hc24, hlam, hphi, u2ehi2]
    · linarith only [h1, hlam, hphi, ht23, u2ehi0, u3elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h87 | h87
    · rcases m.htr 0 2 4 (by decide) (by decide) with h88 | h88
      · rcases m.htr 0 2 5 (by decide) (by decide) with h89 | h89
        · rcases m.htr 0 3 5 (by decide) (by decide) with h90 | h90
          · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
            · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
              · rcases m.htr 1 2 5 (by decide) (by decide) with h93 | h93
                · rcases m.htr 1 3 5 (by decide) (by decide) with h94 | h94
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h95 | h95
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h96 | h96
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h97 | h97
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h98 | h98
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h99 | h99
                            · rcases h2bigk with h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c | h100c
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h0, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h0, h96, h99, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p100_1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                rcases p100_3 (m.d 0 2) (by simp) with h104 | h104
                                · rcases p100_3 (m.d 1 2) (by simp) with h105 | h105
                                  · rcases p100_3 (m.d 2 3) (by simp) with h106 | h106
                                    · linarith only [h106, h87, hlam]
                                    · linarith only [h106, h96, hlam]
                                  · linarith only [h0, h105, hlam, p100_1]
                                · linarith only [h104, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                rcases p100_3 (m.d 0 2) (by simp) with h111 | h111
                                · rcases p100_3 (m.d 1 2) (by simp) with h112 | h112
                                  · rcases p100_3 (m.d 2 3) (by simp) with h113 | h113
                                    · linarith only [h113, h87, hlam]
                                    · linarith only [h113, h97, hlam]
                                  · linarith only [h112, h93, hlam]
                                · linarith only [h111, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h87, h96, h99, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p100_1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h96, h99, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p100_1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                rcases p100_3 (m.d 0 2) (by simp) with h121 | h121
                                · linarith only [h0, h121, hlam]
                                · linarith only [h121, h88, hlam]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                rcases p100_3 (m.d 0 2) (by simp) with h124 | h124
                                · linarith only [h0, h124, hlam]
                                · linarith only [h124, h89, hlam]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h87, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h92, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h87, h98, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p100_1, u2ehi4]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h87, hlam, hphi, ht23, p100_1, u2ehi4, u3elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h88, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hc24, hlam, hphi, p100_1, u2ehi1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h96, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h87, h96, hlam, hphi, ht23, p100_1, u2ehi4, u3elo0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h89, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h93, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h97, hlam, p100_0]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [h98, hlam, p100_1]
                              · have p100_0 := h100c.1
                                have p100_1 := h100c.2.1
                                have p100_2 := h100c.2.2.1
                                have p100_3 := h100c.2.2.2
                                linarith only [hlam, p100_0]
                            · rcases h2bigk with h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c | h142c
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h0, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h0, h96, h98, h99, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h0, h98, h99, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                rcases p142_3 (m.d 0 2) (by simp) with h147 | h147
                                · rcases p142_3 (m.d 1 2) (by simp) with h148 | h148
                                  · rcases p142_3 (m.d 2 3) (by simp) with h149 | h149
                                    · linarith only [h149, h87, hlam]
                                    · linarith only [h149, h97, hlam]
                                  · linarith only [h148, h93, hlam]
                                · linarith only [h147, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h87, h96, h98, h99, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h96, h98, h99, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h98, h99, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p142_1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                rcases p142_3 (m.d 0 2) (by simp) with h158 | h158
                                · linarith only [h0, h158, hlam]
                                · linarith only [h158, h89, hlam]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h87, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h92, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h87, h98, h99, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p142_1, u3elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h87, hlam, hphi, ht23, p142_1, u2ehi4, u3elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h88, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hc24, hlam, hphi, p142_1, u2ehi1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h96, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h87, h96, hlam, hphi, ht23, p142_1, u2ehi4, u3elo0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h89, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h93, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h97, hlam, p142_0]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [h98, hlam, p142_1]
                              · have p142_0 := h142c.1
                                have p142_1 := h142c.2.1
                                have p142_2 := h142c.2.2.1
                                have p142_3 := h142c.2.2.2
                                linarith only [hlam, p142_0]
                          · linarith only [h90, h91, h98, hlam, hphi, ht23, u2ehi3, u3elo0]
                        · linarith only [h97, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h96, hlam, hphi, ht23, u2ehi2, u3elo3]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h179 | h179
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h180 | h180
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h181 | h181
                          · linarith only [h179, h181, h92, h93, h95, hlam, hphi, ht23, u2ehi4, u3elo1]
                          · linarith only [h181, h90, h91, hlam, hphi, ht23, u2ehi3, u3elo0]
                        · linarith only [h180, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h179, hlam, hphi, ht23, u2ehi2, u3elo3]
                  · linarith only [h90, h94, hc13, hlam, hphi, u3elo0]
                · linarith only [h0, h87, h93, hc25, hlam, hphi, u2ehi2]
              · linarith only [h0, h87, h92, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h189 | h189
              · rcases m.htr 1 2 5 (by decide) (by decide) with h190 | h190
                · rcases m.htr 1 3 5 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h192 | h192
                    · linarith only [h191, h192, h88, h91, hlam, hphi, ht23, u2ehi3, u3elo1]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h194 | h194
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h195 | h195
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h196 | h196
                          · linarith only [h196, h88, h91, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h198 | h198
                            · linarith only [h194, h198, h87, h88, h91, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases h2bigk with h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c | h200c
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h0, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                rcases p200_3 (m.d 0 2) (by simp) with h203 | h203
                                · rcases p200_3 (m.d 1 2) (by simp) with h204 | h204
                                  · rcases p200_3 (m.d 2 3) (by simp) with h205 | h205
                                    · linarith only [h205, hlam, p200_0]
                                    · rcases p200_3 (m.d 2 4) (by simp) with h207 | h207
                                      · linarith only [h207, h88, hlam]
                                      · rcases p200_3 (m.d 2 5) (by simp) with h209 | h209
                                        · linarith only [h209, h89, hlam]
                                        · rcases h5bigk with h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c | h211c
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [hlam, p211_0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h190, h196, h90, hlam, hphi, ht23, p211_1, u2ehi3, u3elo0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h196, h90, hlam, hphi, ht23, p211_1, u2ehi3, u3elo0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            rcases p211_3 (m.d 0 5) (by simp) with h215 | h215
                                            · rcases p211_3 (m.d 1 5) (by simp) with h216 | h216
                                              · rcases p211_3 (m.d 2 5) (by simp) with h217 | h217
                                                · linarith only [h217, h89, hlam]
                                                · linarith only [h195, h217, hlam]
                                              · linarith only [h191, h216, hlam]
                                            · linarith only [h215, h90, hlam]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h91, hlam, p211_0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h191, h196, h89, hlam, hphi, ht23, p211_1, u2ehi3, u3elo1]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [hlam, p211_0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h191, h196, hlam, hphi, ht23, p211_1, u2ehi3, u3elo1]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            rcases p211_3 (m.d 0 5) (by simp) with h226 | h226
                                            · rcases p211_3 (m.d 1 5) (by simp) with h227 | h227
                                              · rcases p211_3 (m.d 2 5) (by simp) with h228 | h228
                                                · linarith only [h190, h228, hlam]
                                                · linarith only [h195, h228, hlam]
                                              · linarith only [h191, h227, hlam]
                                            · linarith only [h226, h90, hlam]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h192, hlam, p211_0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h89, hlam, p211_1]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h190, hlam, p211_1]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [hlam, p211_0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h0, h195, h198, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p200_1, p211_1]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h196, hlam, p211_0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h90, hlam, p211_1]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h191, hlam, p211_1]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h195, hlam, p211_0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [hlam, p211_0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h198, hlam, p211_0]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h89, hc45, hlam, hphi, ht23, ht34, p211_1, u2ehi4]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [h190, hc45, hlam, hphi, ht23, ht34, p211_1, u2ehi4]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [hc45, hlam, hphi, ht23, ht34, p211_1, u2ehi4]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            rcases p211_3 (m.d 0 5) (by simp) with h247 | h247
                                            · linarith only [h247, h91, hlam]
                                            · linarith only [h247, h90, hlam]
                                          · have p211_0 := h211c.1
                                            have p211_1 := h211c.2.1
                                            have p211_2 := h211c.2.2.1
                                            have p211_3 := h211c.2.2.2
                                            linarith only [hlam, p211_0]
                                  · linarith only [h189, h204, hlam]
                                · linarith only [h203, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                rcases p200_3 (m.d 0 2) (by simp) with h253 | h253
                                · rcases p200_3 (m.d 1 2) (by simp) with h254 | h254
                                  · rcases p200_3 (m.d 2 3) (by simp) with h255 | h255
                                    · linarith only [h255, h87, hlam]
                                    · linarith only [h194, h255, hlam]
                                  · linarith only [h0, h254, hlam, p200_1]
                                · linarith only [h253, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                rcases p200_3 (m.d 0 2) (by simp) with h260 | h260
                                · rcases p200_3 (m.d 1 2) (by simp) with h261 | h261
                                  · rcases p200_3 (m.d 2 3) (by simp) with h262 | h262
                                    · linarith only [h262, h87, hlam]
                                    · linarith only [h195, h262, hlam]
                                  · linarith only [h190, h261, hlam]
                                · linarith only [h260, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h195, h196, h87, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p200_1, u2ehi3]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                rcases p200_3 (m.d 0 2) (by simp) with h269 | h269
                                · linarith only [h0, h269, hlam]
                                · linarith only [h269, h87, hlam]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                rcases p200_3 (m.d 0 2) (by simp) with h272 | h272
                                · linarith only [h0, h272, hlam]
                                · linarith only [h272, h88, hlam]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                rcases p200_3 (m.d 0 2) (by simp) with h275 | h275
                                · linarith only [h0, h275, hlam]
                                · linarith only [h275, h89, hlam]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h87, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h189, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h87, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p200_1, u2ehi3]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h196, h87, hlam, hphi, ht23, p200_1, u2ehi3, u3elo0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h88, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h0, h190, h196, hc01, hc15, hlam, hphi, p200_1]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h194, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h196, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h89, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h190, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [h195, hlam, p200_0]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [hc25, hlam, hphi, p200_1, u2ehi3]
                              · have p200_0 := h200c.1
                                have p200_1 := h200c.2.1
                                have p200_2 := h200c.2.2.1
                                have p200_3 := h200c.2.2.2
                                linarith only [hlam, p200_0]
                        · linarith only [h195, hlam, hphi, ht23, u2ehi2, u3elo4]
                      · linarith only [h194, hlam, hphi, ht23, u2ehi2, u3elo3]
                  · linarith only [h191, h90, hc13, hlam, hphi, u3elo0]
                · linarith only [h0, h190, h89, hlam]
              · linarith only [h0, h189, h88, hc23, hlam, hphi, u2ehi3]
          · linarith only [h87, h90, hlam, hphi, ht23, u2ehi2, u3elo4]
        · linarith only [h88, h89, hc25, hlam, hphi, u2ehi3]
      · linarith only [h87, h88, hc24, hlam, hphi, u2ehi2]
    · linarith only [h87, hlam, hphi, ht23, u2ehi0, u3elo2]

end R2N4
