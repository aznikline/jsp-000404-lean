import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
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
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 4 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                            · linarith only [h0, h13, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                              · linarith only [h0, h10, h13, h15, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                                · linarith only [h0, h10, h13, h17, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h0, h10, h12, h17, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                            · linarith only [h0, h20, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                              · linarith only [h0, h10, h20, h22, h7, hc01, hc35, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                                · linarith only [h0, h12, h24, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h26 | h26
                                  · linarith only [h10, h12, h26, hlam]
                                  · rcases h1bigk with h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c | h28c
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h11, h20, h26, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h11, h20, h26, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      rcases p28_3 (m.d 0 1) (by simp) with h32 | h32
                                      · rcases p28_3 (m.d 1 2) (by simp) with h33 | h33
                                        · linarith only [h0, h33, hlam]
                                        · linarith only [h33, h8, hlam]
                                      · linarith only [h32, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      rcases p28_3 (m.d 0 1) (by simp) with h37 | h37
                                      · rcases p28_3 (m.d 1 2) (by simp) with h38 | h38
                                        · linarith only [h0, h38, hlam]
                                        · linarith only [h38, h9, hlam]
                                      · linarith only [h37, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h11, h20, h26, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h10, h20, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h11, h20, h26, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h1, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h7, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h1, h10, h20, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h11, h20, h26, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h2, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h8, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h10, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h12, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, p28_1, u0ehi0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h9, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h11, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h10, h11, h20, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                        · linarith only [h10, h11, h3, h6, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h63 | h63
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h64 | h64
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h65 | h65
                            · linarith only [h0, h10, h3, h63, h65, hc01, hc35, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h67 | h67
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h68 | h68
                                · linarith only [h0, h68, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h2, h64, h68, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                              · linarith only [h0, h10, h3, h5, h63, h67, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h10, h63, h64, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h74 | h74
                            · linarith only [h0, h10, h7, h74, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h76 | h76
                              · linarith only [h63, h7, h76, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                                · linarith only [h0, h78, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h2, h73, h78, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                            · linarith only [h0, h7, h81, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h83 | h83
                              · linarith only [h0, h63, h7, h83, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h0, h73, h8, h85, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h87 | h87
                                  · linarith only [h0, h3, h5, h73, h8, h87, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                  · rcases h1bigk with h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c | h89c
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p89_1, u4ehi2]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      rcases p89_3 (m.d 0 1) (by simp) with h92 | h92
                                      · rcases p89_3 (m.d 1 2) (by simp) with h93 | h93
                                        · linarith only [h0, h93, hlam]
                                        · linarith only [h7, h93, hlam]
                                      · linarith only [h92, hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      rcases p89_3 (m.d 0 1) (by simp) with h97 | h97
                                      · rcases p89_3 (m.d 1 2) (by simp) with h98 | h98
                                        · linarith only [h0, h98, hlam]
                                        · linarith only [h8, h98, hlam]
                                      · linarith only [h97, hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      rcases p89_3 (m.d 0 1) (by simp) with h102 | h102
                                      · rcases p89_3 (m.d 1 2) (by simp) with h103 | h103
                                        · linarith only [h0, h103, hlam]
                                        · linarith only [h103, h9, hlam]
                                      · linarith only [h102, hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h0, hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      rcases p89_3 (m.d 0 1) (by simp) with h109 | h109
                                      · rcases p89_3 (m.d 1 2) (by simp) with h110 | h110
                                        · rcases p89_3 (m.d 1 3) (by simp) with h111 | h111
                                          · linarith only [h111, h7, hlam]
                                          · rcases p89_3 (m.d 1 4) (by simp) with h113 | h113
                                            · linarith only [h113, h8, hlam]
                                            · linarith only [h10, h113, hlam]
                                        · linarith only [h110, h7, hlam]
                                      · linarith only [h1, h109, hlam]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h0, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p89_1, u4ehi2]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h0, h73, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, p89_1, u4ehi2]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h1, hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h7, hlam, p89_1]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h10, hlam, p89_1]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h63, hlam, p89_1]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h2, hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h8, hlam, p89_1]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h10, h7, h87, hc23, hc45, hlam, hphi, ht34, p89_1]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [hlam, p89_0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h73, hlam, p89_1]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, p89_1, u0ehi0]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h9, hlam, p89_1]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      rcases p89_3 (m.d 0 1) (by simp) with h132 | h132
                                      · rcases p89_3 (m.d 1 2) (by simp) with h133 | h133
                                        · rcases p89_3 (m.d 1 3) (by simp) with h134 | h134
                                          · linarith only [h134, h63, hlam]
                                          · rcases p89_3 (m.d 1 4) (by simp) with h136 | h136
                                            · linarith only [h136, h73, hlam]
                                            · linarith only [h10, h136, hlam]
                                        · linarith only [h133, h7, hlam]
                                      · linarith only [h1, h132, hlam]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [h0, h3, h6, h63, hc01, hlam, hphi, ht0b, ht45, ht5b, p89_1, u4ehi1]
                                    · have p89_0 := h89c.1
                                      have p89_1 := h89c.2.1
                                      have p89_2 := h89c.2.2.1
                                      have p89_3 := h89c.2.2.2
                                      linarith only [hlam, p89_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h143 | h143
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h144 | h144
                        · linarith only [h144, h7, h9, hlam]
                        · linarith only [h0, h143, h144, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h147 | h147
                        · linarith only [h147, h7, h9, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h149 | h149
                          · linarith only [h149, h8, h9, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h151 | h151
                            · linarith only [h0, h143, h151, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h153 | h153
                              · linarith only [h147, h153, h7, h9, hlam]
                              · linarith only [h0, h153, h3, h6, h8, h9, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h156 | h156
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h157 | h157
                      · linarith only [h0, h157, h4, h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h159 | h159
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h160 | h160
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h161 | h161
                            · linarith only [h0, h157, h159, h161, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h163 | h163
                              · linarith only [h0, h161, h163, h3, h5, h7, h8, hc01, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h159, h161, h163, h3, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h156, h160, h8, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h167 | h167
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h168 | h168
                            · linarith only [h168, h7, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h170 | h170
                              · linarith only [h159, h170, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h172 | h172
                                · linarith only [h0, h156, h168, h172, h3, h5, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h156, h167, h172, h8, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h156, h167, h8, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h176 | h176
                      · linarith only [h0, h176, h4, h7, h8, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h178 | h178
                        · linarith only [h156, h178, h7, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h180 | h180
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h181 | h181
                            · linarith only [h0, h176, h181, h4, h7, h8, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h183 | h183
                              · linarith only [h156, h178, h183, h7, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h185 | h185
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h186 | h186
                                  · rcases h1bigk with h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c | h187c
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      rcases p187_3 (m.d 0 1) (by simp) with h189 | h189
                                      · rcases p187_3 (m.d 1 2) (by simp) with h190 | h190
                                        · linarith only [h190, hlam, p187_0]
                                        · rcases p187_3 (m.d 1 3) (by simp) with h192 | h192
                                          · linarith only [h1, h192, hlam]
                                          · rcases p187_3 (m.d 1 4) (by simp) with h194 | h194
                                            · linarith only [h194, h2, hlam]
                                            · linarith only [h194, h8, hlam]
                                      · linarith only [h189, hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      rcases p187_3 (m.d 0 1) (by simp) with h198 | h198
                                      · rcases p187_3 (m.d 1 2) (by simp) with h199 | h199
                                        · linarith only [h0, h199, hlam]
                                        · linarith only [h199, h7, hlam]
                                      · linarith only [h198, hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h180, hc01, hlam, hphi, ht0b, ht45, ht5b, p187_1, u4ehi4]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      rcases p187_3 (m.d 0 1) (by simp) with h204 | h204
                                      · rcases p187_3 (m.d 1 2) (by simp) with h205 | h205
                                        · linarith only [h0, h205, hlam]
                                        · rcases p187_3 (m.d 1 3) (by simp) with h207 | h207
                                          · linarith only [h1, h207, hlam]
                                          · rcases p187_3 (m.d 1 4) (by simp) with h209 | h209
                                            · linarith only [h2, h209, hlam]
                                            · linarith only [h180, h209, hlam]
                                      · linarith only [h204, hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h0, hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h0, h156, h181, h185, h3, h5, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p187_1]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h8, hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h156, hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h1, hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h7, hlam, p187_1]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h176, hlam, p187_1]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h178, hlam, p187_1]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h2, hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h2, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p187_1]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      rcases p187_3 (m.d 0 1) (by simp) with h225 | h225
                                      · rcases p187_3 (m.d 1 2) (by simp) with h226 | h226
                                        · linarith only [h226, h8, hlam]
                                        · linarith only [h226, h7, hlam]
                                      · linarith only [h1, h225, hlam]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h0, h156, h181, h3, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p187_1]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h0, h181, h3, h5, h8, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p187_1, u4ehi1]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h0, h156, h181, h185, h3, h5, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p187_1]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      rcases p187_3 (m.d 0 1) (by simp) with h234 | h234
                                      · rcases p187_3 (m.d 1 2) (by simp) with h235 | h235
                                        · linarith only [h156, h235, hlam]
                                        · linarith only [h235, h7, hlam]
                                      · linarith only [h1, h234, hlam]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [h180, hlam, p187_0]
                                    · have p187_0 := h187c.1
                                      have p187_1 := h187c.2.1
                                      have p187_2 := h187c.2.2.1
                                      have p187_3 := h187c.2.2.2
                                      linarith only [hlam, p187_0]
                                  · linarith only [h181, h186, h7, h8, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h180, h185, h8, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h243 | h243
                            · linarith only [h243, h7, h8, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h245 | h245
                              · linarith only [h0, h178, h243, h245, h3, h5, h7, h8, hc01, hc15, hlam, hphi, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h247 | h247
                                · linarith only [h0, h180, h243, h247, h3, h5, h7, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                                · linarith only [h247, h7, h8, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                  · linarith only [h0, h250, h3, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h252 | h252
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h254 | h254
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h255 | h255
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h256 | h256
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h257 | h257
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h258 | h258
                                · linarith only [h0, h250, h252, h256, h258, h3, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                · linarith only [h250, h252, h253, h255, h258, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h0, h252, h255, h257, h3, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · linarith only [h0, h252, h255, h256, h3, h5, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h250, h252, h255, hlam]
                        · linarith only [h0, h253, h254, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h265 | h265
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h266 | h266
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h267 | h267
                            · linarith only [h0, h253, h265, h267, h3, hc01, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h252, h267, h3, h5, h7, hc01, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h250, h252, h266, hlam]
                        · linarith only [h252, h265, h7, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h272 | h272
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h273 | h273
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h274 | h274
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h275 | h275
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h276 | h276
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h277 | h277
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h278 | h278
                                  · linarith only [h1, h272, h278, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h2, h274, h278, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                                · linarith only [h250, h274, h277, hlam]
                              · linarith only [h273, h276, h7, hlam]
                            · linarith only [h272, h275, h7, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h284 | h284
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h285 | h285
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h286 | h286
                                · linarith only [h0, h274, h286, h4, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h288 | h288
                                  · linarith only [h272, h286, h288, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                                  · rcases h1bigk with h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c | h290c
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      rcases p290_3 (m.d 0 1) (by simp) with h292 | h292
                                      · rcases p290_3 (m.d 1 2) (by simp) with h293 | h293
                                        · linarith only [h293, hlam, p290_0]
                                        · rcases p290_3 (m.d 1 3) (by simp) with h295 | h295
                                          · linarith only [h1, h295, hlam]
                                          · linarith only [h295, h7, hlam]
                                      · linarith only [h292, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h273, h288, hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi3]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      rcases p290_3 (m.d 0 1) (by simp) with h300 | h300
                                      · rcases p290_3 (m.d 1 2) (by simp) with h301 | h301
                                        · linarith only [h0, h301, hlam]
                                        · rcases p290_3 (m.d 1 3) (by simp) with h303 | h303
                                          · linarith only [h1, h303, hlam]
                                          · linarith only [h272, h303, hlam]
                                      · linarith only [h300, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      rcases p290_3 (m.d 0 1) (by simp) with h307 | h307
                                      · rcases p290_3 (m.d 1 2) (by simp) with h308 | h308
                                        · linarith only [h0, h308, hlam]
                                        · rcases p290_3 (m.d 1 3) (by simp) with h310 | h310
                                          · linarith only [h1, h310, hlam]
                                          · linarith only [h273, h310, hlam]
                                      · linarith only [h307, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h0, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h7, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h250, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h252, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h1, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      rcases p290_3 (m.d 0 1) (by simp) with h320 | h320
                                      · rcases p290_3 (m.d 1 2) (by simp) with h321 | h321
                                        · linarith only [h321, h7, hlam]
                                        · rcases p290_3 (m.d 1 3) (by simp) with h323 | h323
                                          · rcases p290_3 (m.d 1 4) (by simp) with h324 | h324
                                            · linarith only [h272, h324, hlam]
                                            · linarith only [h250, h324, hlam]
                                          · linarith only [h323, h7, hlam]
                                      · linarith only [h0, h320, hlam]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h0, h272, h3, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi3]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h0, h273, h288, h3, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi3]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h2, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h250, h286, hc12, hc45, hlam, hphi, ht23, ht34, p290_1]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h272, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h274, hlam, p290_1]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [hc15, hlam, hphi, ht01, p290_1, u0ehi0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      rcases p290_3 (m.d 0 1) (by simp) with h338 | h338
                                      · rcases p290_3 (m.d 1 2) (by simp) with h339 | h339
                                        · linarith only [h252, h339, hlam]
                                        · rcases p290_3 (m.d 1 3) (by simp) with h341 | h341
                                          · rcases p290_3 (m.d 1 4) (by simp) with h342 | h342
                                            · linarith only [h274, h342, hlam]
                                            · linarith only [h250, h342, hlam]
                                          · linarith only [h341, h7, hlam]
                                      · linarith only [h0, h338, hlam]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h273, hlam, p290_0]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [h0, h273, h3, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, p290_1, u4ehi1]
                                    · have p290_0 := h290c.1
                                      have p290_1 := h290c.2.1
                                      have p290_2 := h290c.2.2.1
                                      have p290_3 := h290c.2.2.2
                                      linarith only [hlam, p290_0]
                              · linarith only [h0, h272, h285, h3, h6, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · linarith only [h272, h284, h7, hlam]
                        · linarith only [h0, h272, h273, h3, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h353 | h353
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h354 | h354
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h355 | h355
                            · linarith only [h0, h272, h3, h353, h355, hc01, hc35, hlam, hphi, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h357 | h357
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h358 | h358
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h359 | h359
                                  · linarith only [h0, h3, h353, h355, h359, h5, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                                  · linarith only [h250, h353, h354, h355, h359, h7, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h250, h3, h353, h354, h355, h358, h5, h7, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                              · linarith only [h353, h357, h7, hlam]
                          · linarith only [h272, h353, h354, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h365 | h365
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h366 | h366
                            · linarith only [h0, h272, h3, h365, h366, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi4]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h368 | h368
                              · linarith only [h353, h366, h368, hc13, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h370 | h370
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h371 | h371
                                  · rcases h1bigk with h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c | h372c
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h0, h3, h368, h371, h5, h7, hlam, p372_2]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      rcases p372_3 (m.d 0 1) (by simp) with h375 | h375
                                      · rcases p372_3 (m.d 1 2) (by simp) with h376 | h376
                                        · linarith only [h0, h376, hlam]
                                        · rcases p372_3 (m.d 1 3) (by simp) with h378 | h378
                                          · linarith only [h378, hlam, p372_0]
                                          · rcases p372_3 (m.d 1 4) (by simp) with h380 | h380
                                            · linarith only [h2, h380, hlam]
                                            · linarith only [h272, h380, hlam]
                                      · linarith only [h375, hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h365, hc01, hlam, hphi, ht0b, ht45, ht5b, p372_1, u4ehi4]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      rcases p372_3 (m.d 0 1) (by simp) with h385 | h385
                                      · rcases p372_3 (m.d 1 2) (by simp) with h386 | h386
                                        · linarith only [h0, h386, hlam]
                                        · rcases p372_3 (m.d 1 3) (by simp) with h388 | h388
                                          · linarith only [h1, h388, hlam]
                                          · rcases p372_3 (m.d 1 4) (by simp) with h390 | h390
                                            · linarith only [h2, h390, hlam]
                                            · linarith only [h365, h390, hlam]
                                      · linarith only [h385, hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h0, hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h7, hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h250, hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h252, hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h1, hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h0, h3, h368, h371, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p372_1]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h272, hlam, p372_1]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h353, hlam, p372_1]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h2, hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      rcases p372_3 (m.d 0 1) (by simp) with h405 | h405
                                      · rcases p372_3 (m.d 1 2) (by simp) with h406 | h406
                                        · linarith only [h250, h406, hlam]
                                        · rcases p372_3 (m.d 1 3) (by simp) with h408 | h408
                                          · linarith only [h272, h408, hlam]
                                          · linarith only [h408, h7, hlam]
                                      · linarith only [h0, h405, hlam]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      rcases p372_3 (m.d 0 1) (by simp) with h412 | h412
                                      · rcases p372_3 (m.d 1 2) (by simp) with h413 | h413
                                        · linarith only [h250, h413, hlam]
                                        · rcases p372_3 (m.d 1 3) (by simp) with h415 | h415
                                          · linarith only [h272, h415, hlam]
                                          · rcases p372_3 (m.d 1 4) (by simp) with h417 | h417
                                            · rcases p372_3 (m.d 1 5) (by simp) with h418 | h418
                                              · linarith only [h365, h418, hlam]
                                              · linarith only [h353, h418, hlam]
                                            · linarith only [h272, h417, hlam]
                                      · linarith only [h1, h412, hlam]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h2, h365, hc01, hlam, hphi, ht0b, ht45, ht5b, p372_1, u4ehi4]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h0, h250, h3, h366, h5, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p372_1, u4ehi1]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      rcases p372_3 (m.d 0 1) (by simp) with h426 | h426
                                      · rcases p372_3 (m.d 1 2) (by simp) with h427 | h427
                                        · linarith only [h252, h427, hlam]
                                        · rcases p372_3 (m.d 1 3) (by simp) with h429 | h429
                                          · linarith only [h353, h429, hlam]
                                          · linarith only [h429, h7, hlam]
                                      · linarith only [h0, h426, hlam]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      rcases p372_3 (m.d 0 1) (by simp) with h433 | h433
                                      · rcases p372_3 (m.d 1 2) (by simp) with h434 | h434
                                        · linarith only [h252, h434, hlam]
                                        · rcases p372_3 (m.d 1 3) (by simp) with h436 | h436
                                          · linarith only [h353, h436, hlam]
                                          · rcases p372_3 (m.d 1 4) (by simp) with h438 | h438
                                            · rcases p372_3 (m.d 1 5) (by simp) with h439 | h439
                                              · rcases h3bigk with h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c | h440c
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h250, h365, h366, h5, hlam, p372_1, p440_2]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  rcases p440_3 (m.d 0 3) (by simp) with h443 | h443
                                                  · rcases p440_3 (m.d 1 3) (by simp) with h444 | h444
                                                    · linarith only [h1, h444, hlam]
                                                    · rcases p440_3 (m.d 2 3) (by simp) with h446 | h446
                                                      · linarith only [h3, h446, hlam]
                                                      · rcases p440_3 (m.d 3 4) (by simp) with h448 | h448
                                                        · linarith only [h448, h5, hlam]
                                                        · linarith only [h366, h448, hlam]
                                                  · linarith only [h3, h443, hlam]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h0, h250, h3, h365, h366, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p372_1, p440_1]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h0, h252, h3, h368, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p372_1, p440_1]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h1, hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h7, hlam, p440_1]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h272, hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h353, hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h3, hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h366, h7, hc12, hc34, hlam, hphi, ht23, p440_1]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h366, hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h368, hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h5, hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  rcases p440_3 (m.d 0 3) (by simp) with h465 | h465
                                                  · rcases p440_3 (m.d 1 3) (by simp) with h466 | h466
                                                    · linarith only [h466, hlam, p440_0]
                                                    · rcases p440_3 (m.d 2 3) (by simp) with h468 | h468
                                                      · linarith only [h366, h468, hlam]
                                                      · linarith only [h468, h7, hlam]
                                                  · linarith only [h1, h465, hlam]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h0, h3, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p440_1]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h0, h3, h353, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p440_1]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h6, hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  rcases p440_3 (m.d 0 3) (by simp) with h476 | h476
                                                  · rcases p440_3 (m.d 1 3) (by simp) with h477 | h477
                                                    · linarith only [h477, hlam, p440_0]
                                                    · rcases p440_3 (m.d 2 3) (by simp) with h479 | h479
                                                      · linarith only [h368, h479, hlam]
                                                      · linarith only [h479, h7, hlam]
                                                  · linarith only [h1, h476, hlam]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h7, hc12, hc35, hlam, hphi, ht23, p440_1]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [h371, hlam, p440_0]
                                                · have p440_0 := h440c.1
                                                  have p440_1 := h440c.2.1
                                                  have p440_2 := h440c.2.2.1
                                                  have p440_3 := h440c.2.2.2
                                                  linarith only [hlam, p440_0]
                                              · linarith only [h353, h439, hlam]
                                            · linarith only [h272, h438, hlam]
                                      · linarith only [h1, h433, hlam]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [h365, hlam, p372_0]
                                    · have p372_0 := h372c.1
                                      have p372_1 := h372c.2.1
                                      have p372_2 := h372c.2.2.1
                                      have p372_3 := h372c.2.2.2
                                      linarith only [hlam, p372_0]
                                  · linarith only [h272, h365, h371, hlam]
                                · linarith only [h250, h365, h370, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h493 | h493
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h494 | h494
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h495 | h495
                                · linarith only [h0, h365, h4, h495, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h497 | h497
                                  · linarith only [h0, h3, h493, h495, h497, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                  · rcases h1bigk with h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c | h499c
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h0, h3, h353, h494, h7, hlam, p499_2]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h0, h3, h353, h494, hlam, p499_2]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      rcases p499_3 (m.d 0 1) (by simp) with h503 | h503
                                      · rcases p499_3 (m.d 1 2) (by simp) with h504 | h504
                                        · linarith only [h0, h504, hlam]
                                        · rcases p499_3 (m.d 1 3) (by simp) with h506 | h506
                                          · linarith only [h1, h506, hlam]
                                          · rcases p499_3 (m.d 1 4) (by simp) with h508 | h508
                                            · linarith only [h508, hlam, p499_0]
                                            · rcases p499_3 (m.d 1 5) (by simp) with h510 | h510
                                              · linarith only [h0, h3, h353, h494, h510, hlam]
                                              · linarith only [h365, h510, hlam]
                                      · linarith only [h503, hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      rcases p499_3 (m.d 0 1) (by simp) with h514 | h514
                                      · rcases p499_3 (m.d 1 2) (by simp) with h515 | h515
                                        · linarith only [h0, h515, hlam]
                                        · rcases p499_3 (m.d 1 3) (by simp) with h517 | h517
                                          · linarith only [h1, h517, hlam]
                                          · rcases p499_3 (m.d 1 4) (by simp) with h519 | h519
                                            · linarith only [h2, h519, hlam]
                                            · rcases p499_3 (m.d 1 5) (by simp) with h521 | h521
                                              · linarith only [h521, hlam, p499_0]
                                              · rcases h3bigk with h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c | h523c
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  rcases p523_3 (m.d 0 3) (by simp) with h525 | h525
                                                  · rcases p523_3 (m.d 1 3) (by simp) with h526 | h526
                                                    · linarith only [h1, h526, hlam]
                                                    · rcases p523_3 (m.d 2 3) (by simp) with h528 | h528
                                                      · linarith only [h3, h528, hlam]
                                                      · linarith only [h528, h7, hlam]
                                                  · linarith only [h1, h525, hlam]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h272, h494, h497, h7, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p523_1]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  rcases p523_3 (m.d 0 3) (by simp) with h533 | h533
                                                  · rcases p523_3 (m.d 1 3) (by simp) with h534 | h534
                                                    · linarith only [h1, h534, hlam]
                                                    · rcases p523_3 (m.d 2 3) (by simp) with h536 | h536
                                                      · linarith only [h3, h536, hlam]
                                                      · linarith only [h493, h536, hlam]
                                                  · linarith only [h533, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  rcases p523_3 (m.d 0 3) (by simp) with h540 | h540
                                                  · rcases p523_3 (m.d 1 3) (by simp) with h541 | h541
                                                    · linarith only [h1, h541, hlam]
                                                    · rcases p523_3 (m.d 2 3) (by simp) with h543 | h543
                                                      · linarith only [h3, h543, hlam]
                                                      · linarith only [h494, h543, hlam]
                                                  · linarith only [h540, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h1, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h7, hlam, p523_1]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h272, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h353, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h3, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  rcases p523_3 (m.d 0 3) (by simp) with h553 | h553
                                                  · rcases p523_3 (m.d 1 3) (by simp) with h554 | h554
                                                    · linarith only [h554, h7, hlam]
                                                    · rcases p523_3 (m.d 2 3) (by simp) with h556 | h556
                                                      · rcases p523_3 (m.d 3 4) (by simp) with h557 | h557
                                                        · linarith only [h493, h557, hlam]
                                                        · linarith only [h272, h557, hlam]
                                                      · linarith only [h556, h7, hlam]
                                                  · linarith only [h1, h553, hlam]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h272, h7, hc12, hc23, hlam, hphi, p523_1]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h0, h272, h3, h497, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p523_1]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h5, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h493, h495, h7, hc12, hc45, hlam, hphi, ht23, ht34, p523_1]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h493, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h497, hlam, p523_1]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h6, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h0, h3, h494, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p523_1]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h494, hlam, p523_0]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [h0, h3, h494, hc01, hlam, hphi, ht0b, ht45, ht5b, p523_1, u4ehi3]
                                                · have p523_0 := h523c.1
                                                  have p523_1 := h523c.2.1
                                                  have p523_2 := h523c.2.2.1
                                                  have p523_3 := h523c.2.2.2
                                                  linarith only [hlam, p523_0]
                                      · linarith only [h514, hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h0, hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h7, hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h250, hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h252, hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h1, hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h272, hc12, hc34, hlam, hphi, ht23, p499_1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h272, hlam, p499_1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h353, hlam, p499_1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h2, hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h250, h495, hc12, hc45, hlam, hphi, ht23, ht34, p499_1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h250, h495, hc13, hc45, hlam, hphi, ht34, p499_1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [hlam, p499_0]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h365, hlam, p499_1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h0, h3, h353, h494, hlam, p499_1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h0, h3, h353, h494, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p499_1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h0, h3, h353, h494, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p499_1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [h0, h3, h353, h494, hc01, hlam, hphi, ht0b, ht45, ht5b, p499_1, u4ehi1]
                                    · have p499_0 := h499c.1
                                      have p499_1 := h499c.2.1
                                      have p499_2 := h499c.2.2.1
                                      have p499_3 := h499c.2.2.2
                                      linarith only [hlam, p499_0]
                              · linarith only [h0, h3, h493, h494, h6, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h597 | h597
                              · linarith only [h353, h493, h597, h7, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h599 | h599
                                · linarith only [h0, h365, h4, h599, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h601 | h601
                                  · linarith only [h0, h3, h5, h599, h601, hc01, hlam, hphi, ht0b, ht45, ht5b, u4ehi2]
                                  · linarith only [h493, h601, h7, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h6, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
          · linarith only [h4, hc24, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc23, hlam, hphi, ht01, ht12, u0ehi1]
      · linarith only [h2, hc14, hlam, hphi, ht01, u0ehi0]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

end R2N4
