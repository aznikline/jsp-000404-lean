import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14718000 in
set_option maxHeartbeats 14718000 in
theorem r1l7_13_24_L_I_H_I_s0_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6087 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc05 := m.hcor 0 5 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h6088 | h6088
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6089 | h6089
    · linarith only [h0, h1, h6089, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6091 | h6091
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6092 | h6092
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6093 | h6093
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6094 | h6094
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6095 | h6095
              · linarith only [h0, h1, h6089, h6095, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6097 | h6097
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6098 | h6098
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6099 | h6099
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6100 | h6100
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6101 | h6101
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6102 | h6102
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6103 | h6103
                            · linarith only [h0, h1, h6095, h6097, h6103, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h1, h6095, h6097, h6100, h6103, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h1, h6095, h6102, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h0, h1, h6095, h6097, h6100, h6101, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6108 | h6108
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6109 | h6109
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6110 | h6110
                            · linarith only [h6097, h6100, h6110, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6112 | h6112
                              · linarith only [h6097, h6100, h6108, h6112, hlam]
                              · rcases h3bigk with h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c | h6114c
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h1, hlam, p6114_1]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6089, hlam, p6114_1]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  rcases p6114_3 (m.d 0 3) (by simp) with h6118 | h6118
                                  · rcases p6114_3 (m.d 1 3) (by simp) with h6119 | h6119
                                    · rcases p6114_3 (m.d 2 3) (by simp) with h6120 | h6120
                                      · rcases p6114_3 (m.d 3 4) (by simp) with h6121 | h6121
                                        · linarith only [h6121, hlam, p6114_0]
                                        · rcases p6114_3 (m.d 3 5) (by simp) with h6123 | h6123
                                          · linarith only [h6093, h6123, hlam]
                                          · linarith only [h6112, h6123, hlam]
                                      · linarith only [h6108, h6120, hlam]
                                    · linarith only [h6098, h6119, hlam]
                                  · linarith only [h6118, hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  rcases p6114_3 (m.d 0 3) (by simp) with h6129 | h6129
                                  · rcases p6114_3 (m.d 1 3) (by simp) with h6130 | h6130
                                    · rcases p6114_3 (m.d 2 3) (by simp) with h6131 | h6131
                                      · rcases p6114_3 (m.d 3 4) (by simp) with h6132 | h6132
                                        · linarith only [h6092, h6132, hlam]
                                        · rcases p6114_3 (m.d 3 5) (by simp) with h6134 | h6134
                                          · linarith only [h6134, hlam, p6114_0]
                                          · rcases h4bigk with h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h0, h1, h6091, h6097, h6108, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h0, h1, h6091, h6095, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h0, h1, h6091, h6095, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h0, h1, h6091, h6095, h6097, h6100, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6087, hlam, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6100, h6108, hc34, hc45, hlam, hphi, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h0, h1, h6095, h6097, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6100, hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6091, hlam, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6097, hlam, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h0, h1, h6091, h6095, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6110, hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6092, hlam, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6098, hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6108, hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6112, hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h6094, hlam, p6136_0]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h0, h1, h6091, h6094, h6095, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h0, h1, h6091, h6094, h6095, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [h0, h1, h6091, h6094, h6095, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6136_1]
                                            · have p6136_0 := h6136c.1
                                              have p6136_1 := h6136c.2.1
                                              have p6136_2 := h6136c.2.2.1
                                              have p6136_3 := h6136c.2.2.2
                                              linarith only [hlam, p6136_0]
                                      · linarith only [h6109, h6131, hlam]
                                    · linarith only [h6099, h6130, hlam]
                                  · linarith only [h6129, hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h0, h1, h6095, hc12, hc23, hlam, hphi, p6114_1]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6095, hlam, p6114_1]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h0, h1, h6091, h6094, h6097, h6100, h6108, hlam, p6114_2]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  rcases p6114_3 (m.d 0 3) (by simp) with h6169 | h6169
                                  · linarith only [h1, h6169, hlam]
                                  · linarith only [h6093, h6169, hlam]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h0, h1, h6091, h6094, h6097, h6100, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6114_1]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h0, h1, h6091, h6094, h6097, h6100, h6108, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6114_1]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6089, h6091, h6094, h6097, h6100, h6108, hlam, p6114_2]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  rcases p6114_3 (m.d 0 3) (by simp) with h6176 | h6176
                                  · linarith only [h6089, h6176, hlam]
                                  · linarith only [h6093, h6176, hlam]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6092, hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6098, hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6108, hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6112, hlam, p6114_1]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6093, hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6099, hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h6109, hlam, p6114_0]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [h0, h1, h6091, h6094, h6099, h6100, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6114_1]
                                · have p6114_0 := h6114c.1
                                  have p6114_1 := h6114c.2.1
                                  have p6114_2 := h6114c.2.2.1
                                  have p6114_3 := h6114c.2.2.2
                                  linarith only [hlam, p6114_0]
                          · linarith only [h0, h1, h6091, h6094, h6095, h6099, h6100, h6109, hlam]
                        · linarith only [h0, h1, h6091, h6094, h6095, h6100, h6108, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h6097, h6099, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h6097, h6098, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h6091, h6095, h6097, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6194 | h6194
              · linarith only [h0, h1, h6089, h6194, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6196 | h6196
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6197 | h6197
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6198 | h6198
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6199 | h6199
                      · linarith only [h1, h6087, h6094, h6194, h6199, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6201 | h6201
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6202 | h6202
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6203 | h6203
                            · linarith only [h0, h1, h6094, h6194, h6196, h6203, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6205 | h6205
                              · linarith only [h6092, h6094, h6205, hlam]
                              · rcases h3bigk with h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c | h6207c
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h1, hlam, p6207_1]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h6089, hlam, p6207_1]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  rcases p6207_3 (m.d 0 3) (by simp) with h6211 | h6211
                                  · rcases p6207_3 (m.d 1 3) (by simp) with h6212 | h6212
                                    · rcases p6207_3 (m.d 2 3) (by simp) with h6213 | h6213
                                      · rcases p6207_3 (m.d 3 4) (by simp) with h6214 | h6214
                                        · linarith only [h6214, hlam, p6207_0]
                                        · rcases p6207_3 (m.d 3 5) (by simp) with h6216 | h6216
                                          · linarith only [h6093, h6216, hlam]
                                          · linarith only [h6205, h6216, hlam]
                                      · linarith only [h6201, h6213, hlam]
                                    · linarith only [h6197, h6212, hlam]
                                  · linarith only [h6211, hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  rcases p6207_3 (m.d 0 3) (by simp) with h6222 | h6222
                                  · rcases p6207_3 (m.d 1 3) (by simp) with h6223 | h6223
                                    · rcases p6207_3 (m.d 2 3) (by simp) with h6224 | h6224
                                      · rcases p6207_3 (m.d 3 4) (by simp) with h6225 | h6225
                                        · linarith only [h6092, h6225, hlam]
                                        · rcases p6207_3 (m.d 3 5) (by simp) with h6227 | h6227
                                          · linarith only [h6227, hlam, p6207_0]
                                          · rcases h4bigk with h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c | h6229c
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6094, h6196, h6201, hc34, hc45, hlam, hphi, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6094, h6201, hc34, hc45, hlam, hphi, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6094, hc34, hc45, hlam, hphi, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6094, hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6087, hlam, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h1, h6087, h6194, h6201, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h1, h6088, h6194, h6199, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6199, hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6091, hlam, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6196, hlam, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6091, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6203, hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6092, hlam, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6197, hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6201, hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6205, hlam, p6229_0]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [hc04, hc45, hlam, hphi, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6196, hc24, hc45, hlam, hphi, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [h6201, hc34, hc45, hlam, hphi, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [hc34, hc45, hlam, hphi, p6229_1]
                                            · have p6229_0 := h6229c.1
                                              have p6229_1 := h6229c.2.1
                                              have p6229_2 := h6229c.2.2.1
                                              have p6229_3 := h6229c.2.2.2
                                              linarith only [hlam, p6229_0]
                                      · linarith only [h6202, h6224, hlam]
                                    · linarith only [h6198, h6223, hlam]
                                  · linarith only [h6222, hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h0, h1, h6194, hc12, hc23, hlam, hphi, p6207_1]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h6194, hlam, p6207_1]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h0, h1, h6196, h6201, hlam, p6207_2]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  rcases p6207_3 (m.d 0 3) (by simp) with h6262 | h6262
                                  · linarith only [h1, h6262, hlam]
                                  · linarith only [h6093, h6262, hlam]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h0, h1, h6196, h6201, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6207_1]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h0, h1, h6196, h6201, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6207_1]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h0, h1, h6194, h6196, h6201, hlam, p6207_2]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  rcases p6207_3 (m.d 0 3) (by simp) with h6269 | h6269
                                  · linarith only [h6089, h6269, hlam]
                                  · linarith only [h6093, h6269, hlam]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h6092, hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h6197, hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h6201, hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h6205, hlam, p6207_1]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h6093, hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h6198, hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h6202, hlam, p6207_0]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [h1, h6088, h6198, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6207_1]
                                · have p6207_0 := h6207c.1
                                  have p6207_1 := h6207c.2.1
                                  have p6207_2 := h6207c.2.2.1
                                  have p6207_3 := h6207c.2.2.2
                                  linarith only [hlam, p6207_0]
                          · linarith only [h1, h6088, h6194, h6198, h6202, hlam]
                        · linarith only [h0, h1, h6194, h6201, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h6196, h6198, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h6092, h6196, h6197, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1, h6091, h6194, h6196, hc12, hc23, hlam, hphi]
          · linarith only [h1, h6088, h6093, hlam]
        · linarith only [h0, h1, h6091, h6092, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6289 | h6289
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6290 | h6290
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6291 | h6291
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6292 | h6292
              · linarith only [h0, h1, h6089, h6292, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6294 | h6294
                · linarith only [h0, h1, h6091, h6292, h6294, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6296 | h6296
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6297 | h6297
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6298 | h6298
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6299 | h6299
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6300 | h6300
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6301 | h6301
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6302 | h6302
                              · rcases h3bigk with h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c | h6303c
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h1, hlam, p6303_1]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h6089, hlam, p6303_1]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  rcases p6303_3 (m.d 0 3) (by simp) with h6307 | h6307
                                  · rcases p6303_3 (m.d 1 3) (by simp) with h6308 | h6308
                                    · rcases p6303_3 (m.d 2 3) (by simp) with h6309 | h6309
                                      · rcases p6303_3 (m.d 3 4) (by simp) with h6310 | h6310
                                        · linarith only [h6310, hlam, p6303_0]
                                        · rcases p6303_3 (m.d 3 5) (by simp) with h6312 | h6312
                                          · linarith only [h6290, h6312, hlam]
                                          · rcases h4bigk with h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c | h6314c
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h1, h6087, h6292, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6091, hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h1, h6087, h6292, h6302, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h1, h6087, h6292, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6087, hlam, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6294, hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6302, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h1, h6087, h6292, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h0, h6091, hc12, hc24, hlam, hphi, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6294, hc12, hc24, hlam, hphi, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6299, h6302, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              rcases p6314_3 (m.d 0 4) (by simp) with h6329 | h6329
                                              · linarith only [h6091, h6329, hlam]
                                              · linarith only [h6291, h6329, hlam]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6289, hlam, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6296, hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6299, hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [hc03, hc45, hlam, hphi, ht0b, ht5b, p6303_1, p6314_1]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6291, hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6298, hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6301, hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [h6302, hlam, p6314_0]
                                            · have p6314_0 := h6314c.1
                                              have p6314_1 := h6314c.2.1
                                              have p6314_2 := h6314c.2.2.1
                                              have p6314_3 := h6314c.2.2.2
                                              linarith only [hlam, p6314_0]
                                      · linarith only [h6299, h6309, hlam]
                                    · linarith only [h6296, h6308, hlam]
                                  · linarith only [h6307, hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  rcases p6303_3 (m.d 0 3) (by simp) with h6345 | h6345
                                  · rcases p6303_3 (m.d 1 3) (by simp) with h6346 | h6346
                                    · rcases p6303_3 (m.d 2 3) (by simp) with h6347 | h6347
                                      · rcases p6303_3 (m.d 3 4) (by simp) with h6348 | h6348
                                        · linarith only [h6289, h6348, hlam]
                                        · linarith only [h6302, h6348, hlam]
                                      · linarith only [h6300, h6347, hlam]
                                    · linarith only [h6297, h6346, hlam]
                                  · linarith only [h6345, hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h0, h1, h6292, hc12, hc23, hlam, hphi, p6303_1]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h6292, hlam, p6303_1]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  rcases p6303_3 (m.d 0 3) (by simp) with h6357 | h6357
                                  · linarith only [h1, h6357, hlam]
                                  · linarith only [h6289, h6357, hlam]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  rcases p6303_3 (m.d 0 3) (by simp) with h6360 | h6360
                                  · linarith only [h1, h6360, hlam]
                                  · linarith only [h6290, h6360, hlam]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h1, h6087, h6296, h6302, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6303_1]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h1, h6087, h6296, h6302, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6303_1]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  rcases p6303_3 (m.d 0 3) (by simp) with h6366 | h6366
                                  · linarith only [h6089, h6366, hlam]
                                  · linarith only [h6289, h6366, hlam]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  rcases p6303_3 (m.d 0 3) (by simp) with h6369 | h6369
                                  · linarith only [h6089, h6369, hlam]
                                  · linarith only [h6290, h6369, hlam]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h6289, hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h6296, hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h6299, hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h1, h6087, h6296, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b, p6303_1]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h6290, hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h6297, hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h6300, hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [h6302, hlam, p6303_0]
                                · have p6303_0 := h6303c.1
                                  have p6303_1 := h6303c.2.1
                                  have p6303_2 := h6303c.2.2.1
                                  have p6303_3 := h6303c.2.2.2
                                  linarith only [hlam, p6303_0]
                              · linarith only [h1, h6087, h6292, h6298, h6302, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h1, h6087, h6292, h6298, h6301, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h1, h6087, h6292, h6298, h6300, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h6087, h6292, h6298, h6299, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h6087, h6291, h6292, h6294, h6298, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h1, h6297, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h6087, h6289, h6294, h6296, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6389 | h6389
              · linarith only [h0, h1, h6089, h6389, hlam]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6391 | h6391
                · linarith only [h0, h6091, h6391, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6393 | h6393
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6394 | h6394
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6395 | h6395
                      · linarith only [h1, h6087, h6291, h6395, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6397 | h6397
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6398 | h6398
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6399 | h6399
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6400 | h6400
                              · linarith only [h6087, h6291, h6393, h6400, hlam]
                              · rcases h3bigk with h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c | h6402c
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h1, hlam, p6402_1]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h6089, hlam, p6402_1]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  rcases p6402_3 (m.d 0 3) (by simp) with h6406 | h6406
                                  · rcases p6402_3 (m.d 1 3) (by simp) with h6407 | h6407
                                    · rcases p6402_3 (m.d 2 3) (by simp) with h6408 | h6408
                                      · rcases p6402_3 (m.d 3 4) (by simp) with h6409 | h6409
                                        · linarith only [h6409, hlam, p6402_0]
                                        · rcases p6402_3 (m.d 3 5) (by simp) with h6411 | h6411
                                          · linarith only [h6290, h6411, hlam]
                                          · linarith only [h6400, h6411, hlam]
                                      · linarith only [h6397, h6408, hlam]
                                    · linarith only [h6393, h6407, hlam]
                                  · linarith only [h6406, hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  rcases p6402_3 (m.d 0 3) (by simp) with h6417 | h6417
                                  · rcases p6402_3 (m.d 1 3) (by simp) with h6418 | h6418
                                    · rcases p6402_3 (m.d 2 3) (by simp) with h6419 | h6419
                                      · rcases p6402_3 (m.d 3 4) (by simp) with h6420 | h6420
                                        · linarith only [h6289, h6420, hlam]
                                        · rcases p6402_3 (m.d 3 5) (by simp) with h6422 | h6422
                                          · linarith only [h6422, hlam, p6402_0]
                                          · rcases h4bigk with h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6291, h6391, h6399, hc12, hc24, hlam, hphi, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6091, hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6291, h6399, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6291, hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6087, hlam, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6391, hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6088, h6395, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6395, hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h0, h6091, hc12, hc24, hlam, hphi, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6391, hc12, hc24, hlam, hphi, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              rcases p6424_3 (m.d 0 4) (by simp) with h6438 | h6438
                                              · linarith only [h6091, h6438, hlam]
                                              · linarith only [h6289, h6438, hlam]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h0, h6091, h6291, h6397, hc12, hc23, hlam, hphi, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6289, hlam, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6393, hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6397, hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6400, hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h0, h6091, hc12, hc45, hlam, hphi, ht23, ht34, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6391, hc12, hc45, hlam, hphi, ht23, ht34, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6399, hlam, p6424_0]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [h6397, h6399, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6424_1]
                                            · have p6424_0 := h6424c.1
                                              have p6424_1 := h6424c.2.1
                                              have p6424_2 := h6424c.2.2.1
                                              have p6424_3 := h6424c.2.2.2
                                              linarith only [hlam, p6424_0]
                                      · linarith only [h6398, h6419, hlam]
                                    · linarith only [h6394, h6418, hlam]
                                  · linarith only [h6417, hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h0, h1, h6389, hc12, hc23, hlam, hphi, p6402_1]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h6389, hlam, p6402_1]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  rcases p6402_3 (m.d 0 3) (by simp) with h6458 | h6458
                                  · linarith only [h1, h6458, hlam]
                                  · linarith only [h6289, h6458, hlam]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  rcases p6402_3 (m.d 0 3) (by simp) with h6461 | h6461
                                  · linarith only [h1, h6461, hlam]
                                  · linarith only [h6290, h6461, hlam]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h1, h6088, h6391, h6395, hc12, hc23, hlam, hphi, p6402_1]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h1, h6088, h6391, h6395, hc12, hc23, hlam, hphi, p6402_1]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  rcases p6402_3 (m.d 0 3) (by simp) with h6467 | h6467
                                  · linarith only [h6089, h6467, hlam]
                                  · linarith only [h6289, h6467, hlam]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  rcases p6402_3 (m.d 0 3) (by simp) with h6470 | h6470
                                  · linarith only [h6089, h6470, hlam]
                                  · linarith only [h6290, h6470, hlam]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h6289, hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h6393, hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h6397, hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h6400, hlam, p6402_1]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h6290, hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h6394, hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h6398, hlam, p6402_0]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [h1, h6088, h6389, h6394, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6402_1]
                                · have p6402_0 := h6402c.1
                                  have p6402_1 := h6402c.2.1
                                  have p6402_2 := h6402c.2.2.1
                                  have p6402_3 := h6402c.2.2.2
                                  linarith only [hlam, p6402_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6483 | h6483
                              · linarith only [h0, h6091, h6399, h6483, hc12, hc34, hlam, hphi, ht23]
                              · rcases h3bigk with h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c | h6485c
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h1, hlam, p6485_1]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h6089, hlam, p6485_1]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  rcases p6485_3 (m.d 0 3) (by simp) with h6489 | h6489
                                  · rcases p6485_3 (m.d 1 3) (by simp) with h6490 | h6490
                                    · rcases p6485_3 (m.d 2 3) (by simp) with h6491 | h6491
                                      · rcases p6485_3 (m.d 3 4) (by simp) with h6492 | h6492
                                        · linarith only [h6492, hlam, p6485_0]
                                        · rcases p6485_3 (m.d 3 5) (by simp) with h6494 | h6494
                                          · linarith only [h6290, h6494, hlam]
                                          · linarith only [h6483, h6494, hlam]
                                      · linarith only [h6397, h6491, hlam]
                                    · linarith only [h6393, h6490, hlam]
                                  · linarith only [h6489, hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  rcases p6485_3 (m.d 0 3) (by simp) with h6500 | h6500
                                  · rcases p6485_3 (m.d 1 3) (by simp) with h6501 | h6501
                                    · rcases p6485_3 (m.d 2 3) (by simp) with h6502 | h6502
                                      · rcases p6485_3 (m.d 3 4) (by simp) with h6503 | h6503
                                        · linarith only [h6289, h6503, hlam]
                                        · rcases p6485_3 (m.d 3 5) (by simp) with h6505 | h6505
                                          · linarith only [h6505, hlam, p6485_0]
                                          · rcases h4bigk with h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h1, h6087, h6389, h6393, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6091, hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6091, h6399, hc34, hc45, hlam, hphi, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6291, hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6087, hlam, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6391, hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h1, h6087, h6389, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6395, hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6399, hc04, hc45, hlam, hphi, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6399, hc14, hc45, hlam, hphi, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6399, hc34, hc45, hlam, hphi, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6399, hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6289, hlam, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6393, hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6397, hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6483, hlam, p6507_0]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h0, h6091, hc12, hc45, hlam, hphi, ht23, ht34, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [h6391, hc12, hc45, hlam, hphi, ht23, ht34, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [hc24, hc45, hlam, hphi, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [hc34, hc45, hlam, hphi, p6507_1]
                                            · have p6507_0 := h6507c.1
                                              have p6507_1 := h6507c.2.1
                                              have p6507_2 := h6507c.2.2.1
                                              have p6507_3 := h6507c.2.2.2
                                              linarith only [hlam, p6507_0]
                                      · linarith only [h6398, h6502, hlam]
                                    · linarith only [h6394, h6501, hlam]
                                  · linarith only [h6500, hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h0, h1, h6389, hc12, hc23, hlam, hphi, p6485_1]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h6389, hlam, p6485_1]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  rcases p6485_3 (m.d 0 3) (by simp) with h6539 | h6539
                                  · linarith only [h1, h6539, hlam]
                                  · linarith only [h6289, h6539, hlam]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  rcases p6485_3 (m.d 0 3) (by simp) with h6542 | h6542
                                  · linarith only [h1, h6542, hlam]
                                  · linarith only [h6290, h6542, hlam]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h1, h6088, h6391, h6395, hc12, hc23, hlam, hphi, p6485_1]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h1, h6088, h6391, h6395, hc12, hc23, hlam, hphi, p6485_1]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  rcases p6485_3 (m.d 0 3) (by simp) with h6548 | h6548
                                  · linarith only [h6089, h6548, hlam]
                                  · linarith only [h6289, h6548, hlam]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  rcases p6485_3 (m.d 0 3) (by simp) with h6551 | h6551
                                  · linarith only [h6089, h6551, hlam]
                                  · linarith only [h6290, h6551, hlam]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h6289, hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h6393, hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h6397, hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h6483, hlam, p6485_1]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h6290, hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h6394, hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h6398, hlam, p6485_0]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [h1, h6088, h6394, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6485_1]
                                · have p6485_0 := h6485c.1
                                  have p6485_1 := h6485c.2.1
                                  have p6485_2 := h6485c.2.2.1
                                  have p6485_3 := h6485c.2.2.2
                                  linarith only [hlam, p6485_0]
                          · linarith only [h1, h6088, h6389, h6394, h6398, hlam]
                        · linarith only [h1, h6088, h6389, h6391, h6395, h6397, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h6087, h6391, h6394, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h6087, h6391, h6393, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h6088, h6290, hlam]
        · linarith only [h1, h6087, h6289, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6570 | h6570
    · linarith only [h0, h1, h6570, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6572 | h6572
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6573 | h6573
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6574 | h6574
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6575 | h6575
            · linarith only [h0, h6088, h6572, h6575, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6577 | h6577
              · linarith only [h0, h1, h6570, h6577, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6579 | h6579
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6580 | h6580
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6581 | h6581
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6582 | h6582
                      · linarith only [h6087, h6088, h6575, h6582, hlam]
                      · linarith only [h0, h6088, h6579, h6582, hc24, hc45, hlam, hphi]
                    · linarith only [h0, h1, h6574, h6579, h6581, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h6579, h6580, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h6570, h6572, h6579, hc12, hc23, hlam, hphi]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6588 | h6588
            · linarith only [h0, h1, h6572, h6574, h6588, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6590 | h6590
              · linarith only [h0, h1, h6574, h6590, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6592 | h6592
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6593 | h6593
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6594 | h6594
                    · linarith only [h0, h1, h6574, h6592, h6594, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h1, h6592, h6594, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h0, h1, h6592, h6593, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h6570, h6572, h6592, hc12, hc23, hlam, hphi]
        · linarith only [h1, h6087, h6573, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6600 | h6600
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6601 | h6601
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6602 | h6602
            · linarith only [h6087, h6088, h6602, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6604 | h6604
              · linarith only [h0, h1, h6570, h6604, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6606 | h6606
                · linarith only [h0, h6572, h6606, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6608 | h6608
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6609 | h6609
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h6610 | h6610
                      · linarith only [h6087, h6088, h6572, h6602, h6604, h6609, h6610, hc02, hc23, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h6612 | h6612
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h6613 | h6613
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h6614 | h6614
                            · linarith only [h0, h6088, h6610, h6614, hc12, hc24, hlam, hphi]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h6616 | h6616
                              · linarith only [h6087, h6088, h6608, h6609, h6614, h6616, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases h3bigk with h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c | h6618c
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h1, hlam, p6618_1]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6570, hlam, p6618_1]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  rcases p6618_3 (m.d 0 3) (by simp) with h6622 | h6622
                                  · rcases p6618_3 (m.d 1 3) (by simp) with h6623 | h6623
                                    · rcases p6618_3 (m.d 2 3) (by simp) with h6624 | h6624
                                      · rcases p6618_3 (m.d 3 4) (by simp) with h6625 | h6625
                                        · linarith only [h6625, hlam, p6618_0]
                                        · rcases p6618_3 (m.d 3 5) (by simp) with h6627 | h6627
                                          · linarith only [h6601, h6627, hlam]
                                          · linarith only [h6616, h6627, hlam]
                                      · linarith only [h6612, h6624, hlam]
                                    · linarith only [h6608, h6623, hlam]
                                  · linarith only [h6622, hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  rcases p6618_3 (m.d 0 3) (by simp) with h6633 | h6633
                                  · rcases p6618_3 (m.d 1 3) (by simp) with h6634 | h6634
                                    · rcases p6618_3 (m.d 2 3) (by simp) with h6635 | h6635
                                      · rcases p6618_3 (m.d 3 4) (by simp) with h6636 | h6636
                                        · linarith only [h6600, h6636, hlam]
                                        · rcases p6618_3 (m.d 3 5) (by simp) with h6638 | h6638
                                          · linarith only [h6638, hlam, p6618_0]
                                          · rcases h4bigk with h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6087, h6088, h6606, h6610, hc12, hc45, hlam, hphi, ht23, ht34, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6572, hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6087, h6088, h6610, hc34, hc45, hlam, hphi, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6602, hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6087, hlam, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6606, hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6087, h6088, h6610, hc34, hc45, hlam, hphi, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6610, hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6614, hc04, hc45, hlam, hphi, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6614, hc14, hc45, hlam, hphi, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6614, hc34, hc45, hlam, hphi, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6614, hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6600, hlam, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6608, hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6612, hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6616, hlam, p6640_0]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h0, h6572, hc12, hc45, hlam, hphi, ht23, ht34, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [h6606, hc12, hc45, hlam, hphi, ht23, ht34, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [hc24, hc45, hlam, hphi, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [hc34, hc45, hlam, hphi, p6640_1]
                                            · have p6640_0 := h6640c.1
                                              have p6640_1 := h6640c.2.1
                                              have p6640_2 := h6640c.2.2.1
                                              have p6640_3 := h6640c.2.2.2
                                              linarith only [hlam, p6640_0]
                                      · linarith only [h6613, h6635, hlam]
                                    · linarith only [h6609, h6634, hlam]
                                  · linarith only [h6633, hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6087, h6088, h6601, h6604, h6606, hc12, hc23, hlam, hphi, p6618_1]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6604, hlam, p6618_1]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  rcases p6618_3 (m.d 0 3) (by simp) with h6672 | h6672
                                  · linarith only [h1, h6672, hlam]
                                  · linarith only [h6600, h6672, hlam]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  rcases p6618_3 (m.d 0 3) (by simp) with h6675 | h6675
                                  · linarith only [h1, h6675, hlam]
                                  · linarith only [h6601, h6675, hlam]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6087, h6088, h6601, h6606, hc12, hc23, hlam, hphi, p6618_1]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h1, h6087, h6606, hc12, hc23, hlam, hphi, p6618_1]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  rcases p6618_3 (m.d 0 3) (by simp) with h6681 | h6681
                                  · linarith only [h6570, h6681, hlam]
                                  · linarith only [h6600, h6681, hlam]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  rcases p6618_3 (m.d 0 3) (by simp) with h6684 | h6684
                                  · linarith only [h6570, h6684, hlam]
                                  · linarith only [h6601, h6684, hlam]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6600, hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6608, hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6612, hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6616, hlam, p6618_1]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6601, hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6609, hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [h6613, hlam, p6618_0]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  rcases p6618_3 (m.d 0 3) (by simp) with h6695 | h6695
                                  · rcases p6618_3 (m.d 1 3) (by simp) with h6696 | h6696
                                    · rcases p6618_3 (m.d 2 3) (by simp) with h6697 | h6697
                                      · rcases p6618_3 (m.d 3 4) (by simp) with h6698 | h6698
                                        · linarith only [h6616, h6698, hlam]
                                        · rcases p6618_3 (m.d 3 5) (by simp) with h6700 | h6700
                                          · rcases h4bigk with h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c | h6701c
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h1, h6087, h6088, h6601, h6604, h6606, hc12, hc15, hc23, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6618_1, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6572, hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h1, h6087, h6604, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6602, hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6087, hlam, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6606, hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h1, h6087, h6604, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6610, hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h0, h6572, hc12, hc24, hlam, hphi, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6606, hc12, hc24, hlam, hphi, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6614, hc34, hc45, hlam, hphi, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6614, hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6600, hlam, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6608, hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6612, hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h6616, hlam, p6701_0]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h0, h6572, hc12, hc45, hlam, hphi, ht23, ht34, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [h1, h6601, h6604, h6606, hc12, hc23, hc34, hc45, hlam, hphi, p6618_1, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [hc24, hc45, hlam, hphi, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [hc34, hc45, hlam, hphi, p6701_1]
                                            · have p6701_0 := h6701c.1
                                              have p6701_1 := h6701c.2.1
                                              have p6701_2 := h6701c.2.2.1
                                              have p6701_3 := h6701c.2.2.2
                                              linarith only [hlam, p6701_0]
                                          · linarith only [h6616, h6700, hlam]
                                      · linarith only [h6612, h6697, hlam]
                                    · linarith only [h6608, h6696, hlam]
                                  · linarith only [h6600, h6695, hlam]
                                · have p6618_0 := h6618c.1
                                  have p6618_1 := h6618c.2.1
                                  have p6618_2 := h6618c.2.2.1
                                  have p6618_3 := h6618c.2.2.2
                                  linarith only [hlam, p6618_0]
                          · linarith only [h1, h6601, h6604, h6613, hlam]
                        · linarith only [h0, h1, h6604, h6612, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h6087, h6606, h6609, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h6087, h6606, h6608, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6736 | h6736
            · linarith only [h1, h6087, h6601, h6736, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6738 | h6738
              · linarith only [h0, h1, h6601, h6738, hc23, hc35, hlam, hphi]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6740 | h6740
                · linarith only [h0, h6572, h6740, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h6742 | h6742
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h6743 | h6743
                    · linarith only [h1, h6087, h6601, h6738, h6740, h6743, hc12, hc23, hlam, hphi]
                    · linarith only [h1, h6087, h6740, h6743, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h6087, h6740, h6742, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h1, h6087, h6600, hlam]

end R2N4
