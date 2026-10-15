import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_H_R_L_I_L_R_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                              · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h11, h14, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                              · linarith only [h0, h17, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h0, h11, h17, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                          · linarith only [h11, h12, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                          · linarith only [h0, h11, h21, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                              · linarith only [h21, h24, h8, hc35, hlam, hphi, u3ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h26 | h26
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h27 | h27
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
                                      linarith only [h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      rcases p28_3 (m.d 0 1) (by simp) with h31 | h31
                                      · rcases p28_3 (m.d 1 2) (by simp) with h32 | h32
                                        · linarith only [h0, h32, hlam]
                                        · linarith only [h32, h8, hlam]
                                      · linarith only [h31, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      rcases p28_3 (m.d 0 1) (by simp) with h36 | h36
                                      · rcases p28_3 (m.d 1 2) (by simp) with h37 | h37
                                        · linarith only [h0, h37, hlam]
                                        · linarith only [h37, h9, hlam]
                                      · linarith only [h36, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      rcases p28_3 (m.d 0 1) (by simp) with h41 | h41
                                      · rcases p28_3 (m.d 1 2) (by simp) with h42 | h42
                                        · linarith only [h0, h42, hlam]
                                        · linarith only [h10, h42, hlam]
                                      · linarith only [h41, hlam, p28_0]
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
                                      linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h24, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h21, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h1, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h8, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h11, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h21, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h2, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h9, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h2, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h0, h11, h21, h4, h6, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h3, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h10, hlam, p28_1]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h3, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p28_1, u3ehi2]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [h23, hlam, p28_0]
                                    · have p28_0 := h28c.1
                                      have p28_1 := h28c.2.1
                                      have p28_2 := h28c.2.2.1
                                      have p28_3 := h28c.2.2.2
                                      linarith only [hlam, p28_0]
                                  · linarith only [h0, h26, h27, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h2, h23, h24, h26, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h68 | h68
                              · linarith only [h0, h68, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h70 | h70
                                · linarith only [h23, h70, h9, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h72 | h72
                                  · linarith only [h0, h11, h23, h4, h6, h72, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h0, h11, h4, h6, h7, h72, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h75 | h75
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h76 | h76
                          · linarith only [h10, h76, h8, hlam]
                          · linarith only [h75, h76, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                          · linarith only [h0, h4, h6, h75, h79, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                            · linarith only [h10, h81, h9, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                              · linarith only [h0, h10, h4, h6, h7, h8, h81, h83, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h10, h81, h85, h9, hlam]
                                · linarith only [h0, h10, h4, h6, h7, h83, h85, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h5, h8, h9, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h90 | h90
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h91 | h91
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h92 | h92
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h93 | h93
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                              · linarith only [h0, h4, h8, h89, h94, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h8, h89, h91, h94, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h97 | h97
                              · linarith only [h0, h4, h8, h89, h97, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h8, h91, h93, h97, hc12, hc45, hlam, hphi, ht23, ht34]
                          · linarith only [h91, h92, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h8, h89, h91, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h102 | h102
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h103 | h103
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h104 | h104
                            · linarith only [h104, h89, h90, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h106 | h106
                              · linarith only [h0, h106, h4, h8, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                              · linarith only [h102, h104, h106, h6, h7, h8, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h102, h103, hc35, hlam, hphi, u3ehi3]
                        · linarith only [h102, h8, h89, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h114 | h114
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h115 | h115
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h116 | h116
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h117 | h117
                                  · rcases h1bigk with h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c | h118c
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      rcases p118_3 (m.d 0 1) (by simp) with h120 | h120
                                      · rcases p118_3 (m.d 1 2) (by simp) with h121 | h121
                                        · linarith only [h121, hlam, p118_0]
                                        · rcases p118_3 (m.d 1 3) (by simp) with h123 | h123
                                          · linarith only [h1, h123, hlam]
                                          · linarith only [h123, h8, hlam]
                                      · linarith only [h120, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h112, h117, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi4]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      rcases p118_3 (m.d 0 1) (by simp) with h128 | h128
                                      · rcases p118_3 (m.d 1 2) (by simp) with h129 | h129
                                        · linarith only [h0, h129, hlam]
                                        · rcases p118_3 (m.d 1 3) (by simp) with h131 | h131
                                          · linarith only [h1, h131, hlam]
                                          · linarith only [h112, h131, hlam]
                                      · linarith only [h128, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      rcases p118_3 (m.d 0 1) (by simp) with h135 | h135
                                      · rcases p118_3 (m.d 1 2) (by simp) with h136 | h136
                                        · linarith only [h0, h136, hlam]
                                        · linarith only [h111, h136, hlam]
                                      · linarith only [h135, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h0, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h8, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h89, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h113, h115, h89, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p118_1, u3ehi4]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h1, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h1, h111, hc01, hc25, hlam, hphi, ht0b, ht5b, p118_1]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h0, h111, h113, h4, h8, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi4]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h0, h113, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi4]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h2, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h111, h113, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi4]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h112, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h0, h113, h115, h4, h89, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p118_1, u3ehi4]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h3, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h111, hlam, p118_1]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h113, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [h114, hlam, p118_0]
                                    · have p118_0 := h118c.1
                                      have p118_1 := h118c.2.1
                                      have p118_2 := h118c.2.2.1
                                      have p118_3 := h118c.2.2.2
                                      linarith only [hlam, p118_0]
                                  · linarith only [h0, h111, h116, h117, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h111, h114, h116, h3, h89, hc01, hc25, hlam, hphi, ht0b, ht5b]
                              · linarith only [h111, h112, h113, h115, h8, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · linarith only [h111, h114, h89, hlam]
                          · linarith only [h112, h113, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h165 | h165
                          · linarith only [h112, h165, h6, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · linarith only [h111, h165, h8, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h168 | h168
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h169 | h169
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h170 | h170
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h171 | h171
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h172 | h172
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h173 | h173
                                  · rcases h1bigk with h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c | h174c
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      rcases p174_3 (m.d 0 1) (by simp) with h176 | h176
                                      · rcases p174_3 (m.d 1 2) (by simp) with h177 | h177
                                        · linarith only [h177, hlam, p174_0]
                                        · rcases p174_3 (m.d 1 3) (by simp) with h179 | h179
                                          · linarith only [h1, h179, hlam]
                                          · linarith only [h179, h8, hlam]
                                      · linarith only [h176, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h168, h173, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p174_1, u3ehi4]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      rcases p174_3 (m.d 0 1) (by simp) with h184 | h184
                                      · rcases p174_3 (m.d 1 2) (by simp) with h185 | h185
                                        · linarith only [h0, h185, hlam]
                                        · rcases p174_3 (m.d 1 3) (by simp) with h187 | h187
                                          · linarith only [h1, h187, hlam]
                                          · linarith only [h168, h187, hlam]
                                      · linarith only [h184, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      rcases p174_3 (m.d 0 1) (by simp) with h191 | h191
                                      · rcases p174_3 (m.d 1 2) (by simp) with h192 | h192
                                        · linarith only [h0, h192, hlam]
                                        · rcases p174_3 (m.d 1 3) (by simp) with h194 | h194
                                          · linarith only [h1, h194, hlam]
                                          · linarith only [h169, h194, hlam]
                                      · linarith only [h191, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h0, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h8, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h89, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h111, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h1, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      rcases p174_3 (m.d 0 1) (by simp) with h204 | h204
                                      · rcases p174_3 (m.d 1 2) (by simp) with h205 | h205
                                        · linarith only [h205, h8, hlam]
                                        · rcases p174_3 (m.d 1 3) (by simp) with h207 | h207
                                          · rcases p174_3 (m.d 1 4) (by simp) with h208 | h208
                                            · linarith only [h168, h208, hlam]
                                            · linarith only [h208, h89, hlam]
                                          · linarith only [h207, h8, hlam]
                                      · linarith only [h0, h204, hlam]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h0, h169, h170, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p174_1, u3ehi4]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h0, h169, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p174_1, u3ehi4]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h2, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      rcases p174_3 (m.d 0 1) (by simp) with h217 | h217
                                      · rcases p174_3 (m.d 1 2) (by simp) with h218 | h218
                                        · linarith only [h218, h89, hlam]
                                        · rcases p174_3 (m.d 1 3) (by simp) with h220 | h220
                                          · rcases p174_3 (m.d 1 4) (by simp) with h221 | h221
                                            · rcases p174_3 (m.d 1 5) (by simp) with h222 | h222
                                              · linarith only [h170, h222, hlam]
                                              · linarith only [h111, h222, hlam]
                                            · linarith only [h221, h89, hlam]
                                          · linarith only [h220, h8, hlam]
                                      · linarith only [h0, h217, hlam]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h168, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h0, h168, h169, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p174_1, u3ehi4]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h3, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      rcases p174_3 (m.d 0 1) (by simp) with h232 | h232
                                      · rcases p174_3 (m.d 1 2) (by simp) with h233 | h233
                                        · linarith only [h111, h233, hlam]
                                        · rcases p174_3 (m.d 1 3) (by simp) with h235 | h235
                                          · rcases p174_3 (m.d 1 4) (by simp) with h236 | h236
                                            · rcases p174_3 (m.d 1 5) (by simp) with h237 | h237
                                              · rcases h4bigk with h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c | h238c
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h0, h170, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, p238_1]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h0, h170, h4, h6, h89, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p174_1, p238_1]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  rcases p238_3 (m.d 0 4) (by simp) with h242 | h242
                                                  · rcases p238_3 (m.d 1 4) (by simp) with h243 | h243
                                                    · linarith only [h2, h243, hlam]
                                                    · linarith only [h168, h243, hlam]
                                                  · linarith only [h242, h6, hlam]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  rcases p238_3 (m.d 0 4) (by simp) with h247 | h247
                                                  · rcases p238_3 (m.d 1 4) (by simp) with h248 | h248
                                                    · linarith only [h2, h248, hlam]
                                                    · linarith only [h170, h248, hlam]
                                                  · linarith only [h247, hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h2, hlam, p238_1]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h89, hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h173, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi4]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  rcases p238_3 (m.d 0 4) (by simp) with h256 | h256
                                                  · rcases p238_3 (m.d 1 4) (by simp) with h257 | h257
                                                    · rcases p238_3 (m.d 2 4) (by simp) with h258 | h258
                                                      · rcases p238_3 (m.d 3 4) (by simp) with h259 | h259
                                                        · linarith only [h168, h259, hlam]
                                                        · linarith only [h173, h259, hlam]
                                                      · linarith only [h172, h258, hlam]
                                                    · linarith only [h257, hlam, p238_0]
                                                  · linarith only [h256, h7, hlam]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h5, hlam, p238_1]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h0, h168, h171, h173, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi4]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h0, h171, h173, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p238_1, u3ehi4]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  rcases p238_3 (m.d 0 4) (by simp) with h269 | h269
                                                  · rcases p238_3 (m.d 1 4) (by simp) with h270 | h270
                                                    · linarith only [h270, h89, hlam]
                                                    · linarith only [h170, h270, hlam]
                                                  · linarith only [h269, h7, hlam]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h6, hlam, p238_1]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h168, hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h171, hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h0, h168, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b, p238_1]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h7, hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h170, hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h172, hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [h173, hlam, p238_0]
                                                · have p238_0 := h238c.1
                                                  have p238_1 := h238c.2.1
                                                  have p238_2 := h238c.2.2.1
                                                  have p238_3 := h238c.2.2.2
                                                  linarith only [hlam, p238_0]
                                              · linarith only [h111, h237, hlam]
                                            · linarith only [h236, h89, hlam]
                                          · linarith only [h235, h8, hlam]
                                      · linarith only [h0, h232, hlam]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h169, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [h170, hlam, p174_0]
                                    · have p174_0 := h174c.1
                                      have p174_1 := h174c.2.1
                                      have p174_2 := h174c.2.2.1
                                      have p174_3 := h174c.2.2.2
                                      linarith only [hlam, p174_0]
                                  · linarith only [h170, h173, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h170, h172, h89, hlam]
                              · linarith only [h168, h171, h8, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h294 | h294
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h295 | h295
                                · linarith only [h0, h168, h170, h294, h295, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h297 | h297
                                  · linarith only [h1, h168, h295, h297, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h1bigk with h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c | h299c
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h0, h295, h4, h6, h7, h89, hlam, p299_2]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h168, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p299_1, u3ehi3]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      rcases p299_3 (m.d 0 1) (by simp) with h303 | h303
                                      · rcases p299_3 (m.d 1 2) (by simp) with h304 | h304
                                        · linarith only [h0, h304, hlam]
                                        · rcases p299_3 (m.d 1 3) (by simp) with h306 | h306
                                          · linarith only [h1, h306, hlam]
                                          · linarith only [h168, h306, hlam]
                                      · linarith only [h303, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      rcases p299_3 (m.d 0 1) (by simp) with h310 | h310
                                      · rcases p299_3 (m.d 1 2) (by simp) with h311 | h311
                                        · linarith only [h0, h311, hlam]
                                        · rcases p299_3 (m.d 1 3) (by simp) with h313 | h313
                                          · linarith only [h1, h313, hlam]
                                          · linarith only [h169, h313, hlam]
                                      · linarith only [h310, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h0, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h8, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h89, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h111, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h1, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      rcases p299_3 (m.d 0 1) (by simp) with h323 | h323
                                      · rcases p299_3 (m.d 1 2) (by simp) with h324 | h324
                                        · linarith only [h324, h8, hlam]
                                        · rcases p299_3 (m.d 1 3) (by simp) with h326 | h326
                                          · rcases p299_3 (m.d 1 4) (by simp) with h327 | h327
                                            · linarith only [h168, h327, hlam]
                                            · linarith only [h327, h89, hlam]
                                          · linarith only [h326, h8, hlam]
                                      · linarith only [h0, h323, hlam]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h0, h168, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p299_1, u3ehi3]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h0, h169, h297, h4, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p299_1, u3ehi3]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h2, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h0, h295, h4, h6, h7, h89, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p299_1]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h168, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h170, hlam, p299_1]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h3, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      rcases p299_3 (m.d 0 1) (by simp) with h341 | h341
                                      · rcases p299_3 (m.d 1 2) (by simp) with h342 | h342
                                        · linarith only [h111, h342, hlam]
                                        · rcases p299_3 (m.d 1 3) (by simp) with h344 | h344
                                          · rcases p299_3 (m.d 1 4) (by simp) with h345 | h345
                                            · linarith only [h170, h345, hlam]
                                            · linarith only [h345, h89, hlam]
                                          · linarith only [h344, h8, hlam]
                                      · linarith only [h0, h341, hlam]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h169, hlam, p299_0]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [h168, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p299_1, u3ehi3]
                                    · have p299_0 := h299c.1
                                      have p299_1 := h299c.2.1
                                      have p299_2 := h299c.2.2.1
                                      have p299_3 := h299c.2.2.2
                                      linarith only [hlam, p299_0]
                              · linarith only [h168, h294, h8, hlam]
                          · linarith only [h168, h169, hc35, hlam, hphi, u3ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h355 | h355
                          · linarith only [h0, h168, h355, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h357 | h357
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h358 | h358
                              · linarith only [h0, h168, h358, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h360 | h360
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h361 | h361
                                  · rcases h1bigk with h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c | h362c
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h0, h358, h4, h6, h8, hlam, p362_2]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      rcases p362_3 (m.d 0 1) (by simp) with h365 | h365
                                      · rcases p362_3 (m.d 1 2) (by simp) with h366 | h366
                                        · linarith only [h0, h366, hlam]
                                        · rcases p362_3 (m.d 1 3) (by simp) with h368 | h368
                                          · linarith only [h368, hlam, p362_0]
                                          · rcases p362_3 (m.d 1 4) (by simp) with h370 | h370
                                            · linarith only [h2, h370, hlam]
                                            · linarith only [h168, h370, hlam]
                                      · linarith only [h365, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      rcases p362_3 (m.d 0 1) (by simp) with h374 | h374
                                      · rcases p362_3 (m.d 1 2) (by simp) with h375 | h375
                                        · linarith only [h0, h375, hlam]
                                        · rcases p362_3 (m.d 1 3) (by simp) with h377 | h377
                                          · linarith only [h1, h377, hlam]
                                          · rcases p362_3 (m.d 1 4) (by simp) with h379 | h379
                                            · linarith only [h379, hlam, p362_0]
                                            · rcases p362_3 (m.d 1 5) (by simp) with h381 | h381
                                              · linarith only [h3, h381, hlam]
                                              · rcases h4bigk with h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c | h383c
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  rcases p383_3 (m.d 0 4) (by simp) with h385 | h385
                                                  · rcases p383_3 (m.d 1 4) (by simp) with h386 | h386
                                                    · linarith only [h2, h386, hlam]
                                                    · rcases p383_3 (m.d 2 4) (by simp) with h388 | h388
                                                      · linarith only [h388, h5, hlam]
                                                      · linarith only [h388, h89, hlam]
                                                  · linarith only [h2, h385, hlam]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  rcases p383_3 (m.d 0 4) (by simp) with h392 | h392
                                                  · rcases p383_3 (m.d 1 4) (by simp) with h393 | h393
                                                    · linarith only [h2, h393, hlam]
                                                    · rcases p383_3 (m.d 2 4) (by simp) with h395 | h395
                                                      · linarith only [h395, h5, hlam]
                                                      · rcases p383_3 (m.d 3 4) (by simp) with h397 | h397
                                                        · linarith only [h397, h6, hlam]
                                                        · linarith only [h358, h397, hlam]
                                                  · linarith only [h392, h5, hlam]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h0, h168, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p383_1, u3ehi1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  rcases p383_3 (m.d 0 4) (by simp) with h402 | h402
                                                  · rcases p383_3 (m.d 1 4) (by simp) with h403 | h403
                                                    · linarith only [h2, h403, hlam]
                                                    · linarith only [h357, h403, hlam]
                                                  · linarith only [h402, hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h2, hlam, p383_1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h89, hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h168, hlam, p383_1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p362_1, p383_1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h5, hlam, p383_1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h0, h5, hlam, p362_2, p383_1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h358, hlam, p383_1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  rcases p383_3 (m.d 0 4) (by simp) with h416 | h416
                                                  · rcases p383_3 (m.d 1 4) (by simp) with h417 | h417
                                                    · linarith only [h417, h89, hlam]
                                                    · linarith only [h357, h417, hlam]
                                                  · linarith only [h416, h7, hlam]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h6, hlam, p383_1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h0, h355, h357, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p383_1, u3ehi1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h0, h4, h6, h89, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p383_1]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  rcases p383_3 (m.d 0 4) (by simp) with h425 | h425
                                                  · rcases p383_3 (m.d 1 4) (by simp) with h426 | h426
                                                    · linarith only [h168, h426, hlam]
                                                    · linarith only [h357, h426, hlam]
                                                  · linarith only [h425, h7, hlam]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h7, hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h357, hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h360, hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [h361, hlam, p383_0]
                                                · have p383_0 := h383c.1
                                                  have p383_1 := h383c.2.1
                                                  have p383_2 := h383c.2.2.1
                                                  have p383_3 := h383c.2.2.2
                                                  linarith only [hlam, p383_0]
                                      · linarith only [h374, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      rcases p362_3 (m.d 0 1) (by simp) with h436 | h436
                                      · rcases p362_3 (m.d 1 2) (by simp) with h437 | h437
                                        · linarith only [h0, h437, hlam]
                                        · rcases p362_3 (m.d 1 3) (by simp) with h439 | h439
                                          · linarith only [h1, h439, hlam]
                                          · rcases p362_3 (m.d 1 4) (by simp) with h441 | h441
                                            · linarith only [h2, h441, hlam]
                                            · linarith only [h357, h441, hlam]
                                      · linarith only [h436, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h0, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h8, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h89, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h111, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h1, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h355, hc12, hc35, hlam, hphi, ht23, p362_1]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h168, hlam, p362_1]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h355, hlam, p362_1]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h2, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      rcases p362_3 (m.d 0 1) (by simp) with h456 | h456
                                      · rcases p362_3 (m.d 1 2) (by simp) with h457 | h457
                                        · linarith only [h457, h89, hlam]
                                        · rcases p362_3 (m.d 1 3) (by simp) with h459 | h459
                                          · linarith only [h168, h459, hlam]
                                          · linarith only [h459, h8, hlam]
                                      · linarith only [h0, h456, hlam]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p362_1, u3ehi1]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h0, h168, h355, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p362_1, u3ehi1]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h3, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      rcases p362_3 (m.d 0 1) (by simp) with h467 | h467
                                      · rcases p362_3 (m.d 1 2) (by simp) with h468 | h468
                                        · linarith only [h111, h468, hlam]
                                        · rcases p362_3 (m.d 1 3) (by simp) with h470 | h470
                                          · linarith only [h355, h470, hlam]
                                          · linarith only [h470, h8, hlam]
                                      · linarith only [h0, h467, hlam]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p362_1, u3ehi1]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [h357, hlam, p362_0]
                                    · have p362_0 := h362c.1
                                      have p362_1 := h362c.2.1
                                      have p362_2 := h362c.2.2.1
                                      have p362_3 := h362c.2.2.2
                                      linarith only [hlam, p362_0]
                                  · linarith only [h358, h361, hc45, hlam, hphi, ht34, u3ehi2]
                                · linarith only [h357, h360, h89, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h479 | h479
                              · linarith only [h0, h168, h4, h479, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h481 | h481
                                · linarith only [h168, h357, h479, h481, hc34, hlam, hphi, u3ehi1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h483 | h483
                                  · linarith only [h0, h4, h481, h483, h6, h89, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                                  · linarith only [h0, h168, h4, h483, h6, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h7, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi3]
              · linarith only [h6, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi2]
            · linarith only [h5, hc24, hlam, hphi, ht01, ht12, u0ehi1]
          · linarith only [h4, hc23, hlam, hphi, ht01, ht12, u0ehi1]
        · linarith only [h3, hc15, hlam, hphi, ht01, u0ehi0]
      · linarith only [h0, h2, hc14, hlam, hphi, ht01, u0ehi1]
    · linarith only [h0, h1, hc13, hlam, hphi, ht01, u0ehi1]
  · linarith only [h0, hc12, hlam, hphi, ht01, u0ehi0]

theorem r1l7_20_12_13_15_H_L_L_0_L_I_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 4 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h3, h8, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h11, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · linarith only [h5, h6, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h15 | h15
              · rcases m.htr 0 4 5 (by decide) (by decide) with h16 | h16
                · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                  · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h17, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · linarith only [h15, h16, h5, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                  · linarith only [h0, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h22, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h25 | h25
                  · linarith only [h0, h25, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h25, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h28 | h28
            · linarith only [h28, h3, h4, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h30 | h30
              · rcases m.htr 0 4 5 (by decide) (by decide) with h31 | h31
                · rcases m.htr 1 2 3 (by decide) (by decide) with h32 | h32
                  · linarith only [h0, h32, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h3, h32, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h3, h31, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                  · linarith only [h0, h37, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h3, h37, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h3, h36, h4, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h41 | h41
          · rcases m.htr 0 3 4 (by decide) (by decide) with h42 | h42
            · rcases m.htr 0 3 5 (by decide) (by decide) with h43 | h43
              · rcases m.htr 0 4 5 (by decide) (by decide) with h44 | h44
                · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                  · linarith only [h3, h41, h45, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h47 | h47
                    · linarith only [h1, h45, h47, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h41, h47, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h50 | h50
                  · linarith only [h3, h50, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h52 | h52
                    · linarith only [h1, h50, h52, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h41, h52, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h42, h43, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h3, h41, h42, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h57 | h57
            · rcases m.htr 0 3 5 (by decide) (by decide) with h58 | h58
              · rcases m.htr 0 4 5 (by decide) (by decide) with h59 | h59
                · rcases m.htr 1 2 3 (by decide) (by decide) with h60 | h60
                  · linarith only [h3, h60, hc02, hlam, hphi, u2elo1]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h62 | h62
                    · linarith only [h0, h41, h62, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h64 | h64
                      · linarith only [h1, h64, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h58, h64, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h67 | h67
                  · linarith only [h0, h3, h41, h58, h67, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h69 | h69
                    · linarith only [h0, h41, h59, h69, hc24, hlam, hphi, ht45, u5elo4]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h71 | h71
                      · linarith only [h1, h71, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h58, h71, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
              · linarith only [h57, h58, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 4 5 (by decide) (by decide) with h76 | h76
                · rcases m.htr 1 2 3 (by decide) (by decide) with h77 | h77
                  · linarith only [h0, h3, h77, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h79 | h79
                    · linarith only [h0, h41, h79, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h81 | h81
                      · linarith only [h1, h81, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h75, h81, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · linarith only [h57, h75, h76, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h85 | h85
                · rcases m.htr 1 2 3 (by decide) (by decide) with h86 | h86
                  · linarith only [h0, h3, h86, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                    · linarith only [h0, h41, h88, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h90 | h90
                      · linarith only [h1, h3, h75, h90, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                        · linarith only [h2, h92, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h85, h92, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                  · linarith only [h0, h3, h95, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                    · linarith only [h0, h41, h97, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h99 | h99
                      · linarith only [h1, h75, h99, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h101 | h101
                        · linarith only [h101, h2, h85, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h103 | h103
                          · linarith only [h0, h103, h3, h57, hc12, hlam, hphi, u2elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                            · linarith only [h0, h103, h105, h3, h75, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h105, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h108 | h108
        · rcases m.htr 0 2 4 (by decide) (by decide) with h109 | h109
          · linarith only [h0, h109, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h111 | h111
            · linarith only [h1, h111, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h113 | h113
              · rcases m.htr 0 4 5 (by decide) (by decide) with h114 | h114
                · rcases m.htr 1 2 3 (by decide) (by decide) with h115 | h115
                  · linarith only [h0, h115, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h108, h109, h115, hc12, hlam, hphi, u2elo3]
                · linarith only [h1, h114, h2, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h119 | h119
                · rcases m.htr 1 2 3 (by decide) (by decide) with h120 | h120
                  · linarith only [h0, h120, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h108, h109, h120, hc12, hlam, hphi, u2elo3]
                · linarith only [h1, h119, h2, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h124 | h124
          · linarith only [h1, h108, h124, h2, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h126 | h126
            · linarith only [h1, h126, h2, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h128 | h128
              · rcases m.htr 0 4 5 (by decide) (by decide) with h129 | h129
                · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
                  · linarith only [h0, h108, h130, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                    · linarith only [h0, h1, h124, h132, h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1, h130, h132, h2, hc12, hlam, hphi, u2elo3]
                · linarith only [h1, h129, h2, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h136 | h136
                · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
                  · linarith only [h0, h108, h137, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h139 | h139
                    · linarith only [h0, h139, h2, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · linarith only [h1, h137, h139, h2, hc12, hlam, hphi, u2elo3]
                · linarith only [h0, h136, h2, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h143 | h143
      · rcases m.htr 0 2 3 (by decide) (by decide) with h144 | h144
        · linarith only [h0, h1, h144, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h146 | h146
          · rcases m.htr 0 3 4 (by decide) (by decide) with h147 | h147
            · rcases m.htr 0 3 5 (by decide) (by decide) with h148 | h148
              · rcases m.htr 0 4 5 (by decide) (by decide) with h149 | h149
                · rcases m.htr 1 2 3 (by decide) (by decide) with h150 | h150
                  · linarith only [h0, h144, h150, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h150, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
                  · linarith only [h0, h153, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h153, hc12, hlam, hphi, u2elo2]
              · linarith only [h147, h148, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h1, h143, h147, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h158 | h158
            · rcases m.htr 0 3 5 (by decide) (by decide) with h159 | h159
              · rcases m.htr 0 4 5 (by decide) (by decide) with h160 | h160
                · rcases m.htr 1 2 3 (by decide) (by decide) with h161 | h161
                  · linarith only [h0, h161, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h161, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h164 | h164
                  · linarith only [h0, h164, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h164, hc12, hlam, hphi, u2elo2]
              · linarith only [h158, h159, hc34, hlam, hphi, ht45, u5elo3]
            · linarith only [h1, h143, h158, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h169 | h169
        · linarith only [h0, h1, h169, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h171 | h171
          · linarith only [h0, h143, h171, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h173 | h173
            · rcases m.htr 0 3 5 (by decide) (by decide) with h174 | h174
              · rcases m.htr 0 4 5 (by decide) (by decide) with h175 | h175
                · rcases m.htr 1 2 3 (by decide) (by decide) with h176 | h176
                  · linarith only [h0, h169, h176, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h176, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h143, h175, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h143, h173, h174, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h181 | h181
              · rcases m.htr 0 4 5 (by decide) (by decide) with h182 | h182
                · rcases m.htr 1 2 3 (by decide) (by decide) with h183 | h183
                  · linarith only [h0, h183, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h0, h1, h183, hc12, hlam, hphi, u2elo2]
                · linarith only [h0, h1, h173, h182, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h1, h181, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h188 | h188
    · rcases m.htr 0 1 4 (by decide) (by decide) with h189 | h189
      · rcases m.htr 0 2 3 (by decide) (by decide) with h190 | h190
        · rcases m.htr 0 2 4 (by decide) (by decide) with h191 | h191
          · rcases m.htr 0 3 4 (by decide) (by decide) with h192 | h192
            · rcases m.htr 0 3 5 (by decide) (by decide) with h193 | h193
              · rcases m.htr 0 4 5 (by decide) (by decide) with h194 | h194
                · rcases m.htr 1 2 3 (by decide) (by decide) with h195 | h195
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h196 | h196
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h197 | h197
                      · linarith only [h0, h188, h197, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h188, h193, h195, h197, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h196, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h195, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h202 | h202
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h203 | h203
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h204 | h204
                      · linarith only [h188, h204, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h193, h204, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h203, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h202, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h192, h193, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h210 | h210
              · rcases m.htr 0 4 5 (by decide) (by decide) with h211 | h211
                · rcases m.htr 1 2 3 (by decide) (by decide) with h212 | h212
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h213 | h213
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h214 | h214
                      · linarith only [h188, h214, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h210, h214, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h0, h213, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h212, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h192, h210, h211, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h220 | h220
                · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h222 | h222
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h223 | h223
                      · linarith only [h188, h210, h223, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h225 | h225
                        · linarith only [h0, h189, h225, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                        · linarith only [h0, h189, h220, h225, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                    · linarith only [h0, h222, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h188, h221, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h230 | h230
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h231 | h231
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h232 | h232
                      · linarith only [h188, h210, h232, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h234 | h234
                        · linarith only [h189, h220, h234, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h236 | h236
                          · linarith only [h188, h192, h230, h236, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h238 | h238
                            · linarith only [h188, h210, h230, h238, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h240 | h240
                              · linarith only [h0, h188, h189, h192, h220, h230, h231, h240, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h242 | h242
                                · rcases h3bigk with h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c | h243c
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h230, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p243_1, u0elo2]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h192, h220, h242, hc23, hlam, hphi, ht34, ht45, p243_1, u5elo3]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h192, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h210, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h188, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h0, h188, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p243_1, u2elo1]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h0, h188, h192, h220, h242, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p243_1, u2elo1]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h232, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h190, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h230, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h236, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h238, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    rcases p243_3 (m.d 0 3) (by simp) with h259 | h259
                                    · linarith only [h259, hlam, p243_0]
                                    · rcases p243_3 (m.d 1 3) (by simp) with h261 | h261
                                      · linarith only [h188, h192, h220, h242, h261, hlam]
                                      · rcases p243_3 (m.d 2 3) (by simp) with h263 | h263
                                        · linarith only [h236, h263, hlam]
                                        · rcases p243_3 (m.d 3 4) (by simp) with h265 | h265
                                          · rcases p243_3 (m.d 3 5) (by simp) with h266 | h266
                                            · linarith only [h242, h266, hlam]
                                            · linarith only [h210, h266, hlam]
                                          · linarith only [h265, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    rcases p243_3 (m.d 0 3) (by simp) with h270 | h270
                                    · linarith only [h192, h270, hlam]
                                    · linarith only [h188, h270, hlam]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    rcases p243_3 (m.d 0 3) (by simp) with h273 | h273
                                    · linarith only [h192, h273, hlam]
                                    · linarith only [h190, h273, hlam]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h188, h210, h230, hc23, hc34, hlam, hphi, p243_1]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h188, h230, hc23, hlam, hphi, ht34, ht45, p243_1, u5elo3]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h230, hc23, hlam, hphi, ht34, ht45, p243_1, u5elo3]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [hc23, hlam, hphi, ht34, ht45, p243_1, u5elo3]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [h242, hlam, p243_0]
                                  · have p243_0 := h243c.1
                                    have p243_1 := h243c.2.1
                                    have p243_2 := h243c.2.2.1
                                    have p243_3 := h243c.2.2.2
                                    linarith only [hlam, p243_0]
                                · linarith only [h188, h192, h230, h242, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h0, h231, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h188, h230, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h189, h191, hlam]
        · linarith only [h0, h188, h190, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h288 | h288
        · rcases m.htr 0 2 4 (by decide) (by decide) with h289 | h289
          · rcases m.htr 0 3 4 (by decide) (by decide) with h290 | h290
            · linarith only [h188, h189, h290, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h292 | h292
              · rcases m.htr 0 4 5 (by decide) (by decide) with h293 | h293
                · rcases m.htr 1 2 3 (by decide) (by decide) with h294 | h294
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h295 | h295
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h296 | h296
                      · linarith only [h188, h296, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h188, h189, h292, h295, h296, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h289, h295, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h188, h294, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h188, h189, h293, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h302 | h302
                · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h305 | h305
                      · linarith only [h188, h292, h305, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h308 | h308
                          · linarith only [h188, h290, h302, h303, h308, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h310 | h310
                            · linarith only [h188, h189, h292, h303, h304, h310, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h312 | h312
                              · linarith only [h289, h312, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                              · linarith only [h302, h312, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · linarith only [h189, h289, h302, h307, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h188, h303, h304, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h303, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h188, h189, h302, hc13, hlam, hphi, ht34, ht45, u5elo4]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h319 | h319
            · linarith only [h0, h188, h289, h319, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h321 | h321
              · rcases m.htr 0 4 5 (by decide) (by decide) with h322 | h322
                · rcases m.htr 1 2 3 (by decide) (by decide) with h323 | h323
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h324 | h324
                    · linarith only [h0, h289, h324, hc01, hlam, hphi, ht12, u2elo1]
                    · linarith only [h0, h188, h323, h324, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h323, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h0, h188, h289, h322, hc13, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h329 | h329
                · rcases m.htr 1 2 3 (by decide) (by decide) with h330 | h330
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h331 | h331
                    · linarith only [h0, h188, h289, h330, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h188, h330, h331, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h188, h330, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h188, h189, h329, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h0, h188, h288, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h337 | h337
      · rcases m.htr 0 2 3 (by decide) (by decide) with h338 | h338
        · rcases m.htr 0 2 4 (by decide) (by decide) with h339 | h339
          · rcases m.htr 0 3 4 (by decide) (by decide) with h340 | h340
            · rcases m.htr 0 3 5 (by decide) (by decide) with h341 | h341
              · rcases m.htr 0 4 5 (by decide) (by decide) with h342 | h342
                · rcases m.htr 1 2 3 (by decide) (by decide) with h343 | h343
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h345 | h345
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h346 | h346
                        · linarith only [h337, h346, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h188, h337, h342, h343, h344, h346, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                      · linarith only [h188, h338, h341, h345, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h337, h344, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo3]
                  · linarith only [h0, h337, h338, h343, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h352 | h352
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h353 | h353
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h354 | h354
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h355 | h355
                        · linarith only [h337, h342, h355, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                          · linarith only [h338, h357, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h338, h340, h357, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h188, h354, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h188, h352, h353, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h337, h352, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h188, h337, h341, hc14, hlam, hphi, ht45, u5elo3]
            · linarith only [h188, h337, h340, hlam]
          · linarith only [h0, h337, h339, hlam]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h366 | h366
          · rcases m.htr 0 3 4 (by decide) (by decide) with h367 | h367
            · rcases m.htr 0 3 5 (by decide) (by decide) with h368 | h368
              · rcases m.htr 0 4 5 (by decide) (by decide) with h369 | h369
                · rcases m.htr 1 2 3 (by decide) (by decide) with h370 | h370
                  · linarith only [h0, h338, h370, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h337, h370, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                  · linarith only [h0, h337, h338, h373, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h337, h373, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
              · linarith only [h0, h337, h338, h368, hc14, hlam, hphi, ht45, u5elo3]
            · linarith only [h0, h337, h338, h367, hlam]
          · linarith only [h0, h337, h366, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h379 | h379
        · rcases m.htr 0 2 4 (by decide) (by decide) with h380 | h380
          · rcases m.htr 0 3 4 (by decide) (by decide) with h381 | h381
            · rcases m.htr 0 3 5 (by decide) (by decide) with h382 | h382
              · rcases m.htr 0 4 5 (by decide) (by decide) with h383 | h383
                · rcases m.htr 1 2 3 (by decide) (by decide) with h384 | h384
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h385 | h385
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h386 | h386
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h387 | h387
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
                          · linarith only [h379, h388, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · linarith only [h381, h388, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h337, h383, h387, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h188, h381, h382, h386, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h380, h385, hlam]
                  · linarith only [h0, h384, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h395 | h395
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h396 | h396
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h397 | h397
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h398 | h398
                        · linarith only [h337, h383, h396, h398, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h337, h398, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                      · linarith only [h188, h379, h382, h397, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h380, h396, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h379, h395, hlam]
              · linarith only [h381, h382, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h405 | h405
              · rcases m.htr 0 4 5 (by decide) (by decide) with h406 | h406
                · rcases m.htr 1 2 3 (by decide) (by decide) with h407 | h407
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h408 | h408
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                          · linarith only [h379, h381, h405, h411, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                            · linarith only [h380, h411, h413, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h405, h413, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                        · linarith only [h337, h406, h410, hlam]
                      · linarith only [h188, h405, h409, hlam]
                    · linarith only [h0, h380, h408, hlam]
                  · linarith only [h0, h407, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h381, h405, h406, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h421 | h421
                · rcases m.htr 1 2 3 (by decide) (by decide) with h422 | h422
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h423 | h423
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h424 | h424
                      · linarith only [h188, h405, h422, h424, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h188, h424, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h380, h423, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h422, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h429 | h429
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h430 | h430
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h431 | h431
                      · linarith only [h188, h405, h429, h431, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h188, h431, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h430, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h379, h429, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h436 | h436
            · linarith only [h379, h380, h436, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h438 | h438
              · rcases m.htr 0 4 5 (by decide) (by decide) with h439 | h439
                · rcases m.htr 1 2 3 (by decide) (by decide) with h440 | h440
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h441 | h441
                    · linarith only [h380, h441, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h441, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h379, h440, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h379, h380, h439, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h446 | h446
                · rcases m.htr 1 2 3 (by decide) (by decide) with h447 | h447
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h448 | h448
                    · linarith only [h379, h380, h448, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h448, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h379, h447, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h379, h380, h446, hc23, hlam, hphi, ht34, ht45, u5elo4]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h453 | h453
          · rcases m.htr 0 3 4 (by decide) (by decide) with h454 | h454
            · rcases m.htr 0 3 5 (by decide) (by decide) with h455 | h455
              · rcases m.htr 0 4 5 (by decide) (by decide) with h456 | h456
                · rcases m.htr 1 2 3 (by decide) (by decide) with h457 | h457
                  · linarith only [h379, h453, h457, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h457, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h460 | h460
                  · linarith only [h379, h453, h460, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h460, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h379, h453, h455, hc24, hlam, hphi, ht45, u5elo3]
            · linarith only [h379, h453, h454, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h465 | h465
            · rcases m.htr 0 3 5 (by decide) (by decide) with h466 | h466
              · rcases m.htr 0 4 5 (by decide) (by decide) with h467 | h467
                · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                  · linarith only [h379, h468, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h468, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h471 | h471
                  · linarith only [h0, h379, h471, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h471, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h465, h466, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h475 | h475
              · rcases m.htr 0 4 5 (by decide) (by decide) with h476 | h476
                · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
                  · linarith only [h0, h379, h477, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h477, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h465, h475, h476, hc35, hlam, hphi, u5elo4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h481 | h481
                · rcases m.htr 1 2 3 (by decide) (by decide) with h482 | h482
                  · linarith only [h0, h379, h482, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h482, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h485 | h485
                  · linarith only [h0, h379, h485, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h485, hc01, hlam, hphi, ht12, u2elo2]

end R2N4
