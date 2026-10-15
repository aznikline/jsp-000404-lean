import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S8
import Jsp000404.R1LeavesN7_13S17
import Jsp000404.R1LeavesN7_13S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5137 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h6063 | h6063
  · rcases m.htr 0 2 4 (by decide) (by decide) with h6064 | h6064
    · rcases m.htr 0 2 5 (by decide) (by decide) with h6065 | h6065
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6066 | h6066
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6067 | h6067
          · linarith only [h5135, h5137, h6067, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6069 | h6069
            · linarith only [h5135, h5137, h6066, h6069, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6071 | h6071
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6072 | h6072
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6073 | h6073
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6074 | h6074
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6075 | h6075
                      · linarith only [h5135, h5137, h6067, h6073, h6075, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6077 | h6077
                        · linarith only [h5136, h5137, h6069, h6077, hlam]
                        · linarith only [h5135, h5137, h6074, h6077, hc34, hc45, hlam, hphi]
                    · linarith only [h6066, h6067, h6074, hc13, hc35, hlam, hphi]
                  · linarith only [h0, h6065, h6073, hlam]
                · linarith only [h0, h6064, h6072, hlam]
              · linarith only [h0, h6063, h6071, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6084 | h6084
          · linarith only [h5136, h5137, h6066, h6084, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6086 | h6086
            · linarith only [h5136, h5137, h6086, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6088 | h6088
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6089 | h6089
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6090 | h6090
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6091 | h6091
                    · linarith only [h5135, h5137, h6066, h6090, h6091, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6093 | h6093
                      · linarith only [h5135, h5137, h6084, h6093, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6095 | h6095
                        · linarith only [h5136, h5137, h6066, h6086, h6093, h6095, hc03, hc35, hlam, hphi]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6097 | h6097
                          · linarith only [h5135, h6066, h6088, h6097, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6099 | h6099
                            · linarith only [h5135, h6084, h6088, h6099, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6101 | h6101
                              · linarith only [h5136, h5137, h6089, h6095, h6101, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6103 | h6103
                                · linarith only [h5136, h5137, h6091, h6095, h6103, hc13, hc34, hlam, hphi]
                                · rcases h2bigk with h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c | h6105c
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h0, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    rcases p6105_3 (m.d 0 2) (by simp) with h6108 | h6108
                                    · rcases p6105_3 (m.d 1 2) (by simp) with h6109 | h6109
                                      · rcases p6105_3 (m.d 2 3) (by simp) with h6110 | h6110
                                        · linarith only [h6110, hlam, p6105_0]
                                        · rcases p6105_3 (m.d 2 4) (by simp) with h6112 | h6112
                                          · linarith only [h6064, h6112, hlam]
                                          · linarith only [h6097, h6112, hlam]
                                      · linarith only [h6088, h6109, hlam]
                                    · linarith only [h6108, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    rcases p6105_3 (m.d 0 2) (by simp) with h6117 | h6117
                                    · rcases p6105_3 (m.d 1 2) (by simp) with h6118 | h6118
                                      · rcases p6105_3 (m.d 2 3) (by simp) with h6119 | h6119
                                        · linarith only [h6063, h6119, hlam]
                                        · rcases p6105_3 (m.d 2 4) (by simp) with h6121 | h6121
                                          · linarith only [h6121, hlam, p6105_0]
                                          · rcases p6105_3 (m.d 2 5) (by simp) with h6123 | h6123
                                            · linarith only [h6065, h6123, hlam]
                                            · linarith only [h6101, h6123, hlam]
                                      · linarith only [h6089, h6118, hlam]
                                    · linarith only [h6117, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    rcases p6105_3 (m.d 0 2) (by simp) with h6128 | h6128
                                    · rcases p6105_3 (m.d 1 2) (by simp) with h6129 | h6129
                                      · rcases p6105_3 (m.d 2 3) (by simp) with h6130 | h6130
                                        · linarith only [h6063, h6130, hlam]
                                        · rcases p6105_3 (m.d 2 4) (by simp) with h6132 | h6132
                                          · linarith only [h6064, h6132, hlam]
                                          · rcases p6105_3 (m.d 2 5) (by simp) with h6134 | h6134
                                            · linarith only [h6134, hlam, p6105_0]
                                            · rcases h3bigk with h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c | h6136c
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6066, h6103, hc13, hc45, hlam, hphi, ht34, p6136_1]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6066, h6103, hc23, hc45, hlam, hphi, ht34, p6136_1]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6066, hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6084, hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h5135, hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h0, h5135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6136_1]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6091, hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6093, hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6063, hlam, p6136_1]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6088, hlam, p6136_1]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6097, hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6099, hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6103, hc03, hc45, hlam, hphi, ht34, p6136_1]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6103, hc13, hc45, hlam, hphi, ht34, p6136_1]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6103, hc23, hc45, hlam, hphi, ht34, p6136_1]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h6103, hlam, p6136_0]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                rcases p6136_3 (m.d 0 3) (by simp) with h6157 | h6157
                                                · linarith only [h6157, hlam, p6136_0]
                                                · rcases p6136_3 (m.d 1 3) (by simp) with h6159 | h6159
                                                  · linarith only [h6093, h6159, hlam]
                                                  · rcases p6136_3 (m.d 2 3) (by simp) with h6161 | h6161
                                                    · linarith only [h6099, h6161, hlam]
                                                    · rcases p6136_3 (m.d 3 4) (by simp) with h6163 | h6163
                                                      · linarith only [h6103, h6163, hlam]
                                                      · linarith only [h6066, h6163, hlam]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                rcases p6136_3 (m.d 0 3) (by simp) with h6166 | h6166
                                                · linarith only [h6084, h6166, hlam]
                                                · linarith only [h5135, h6166, hlam]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                rcases p6136_3 (m.d 0 3) (by simp) with h6169 | h6169
                                                · linarith only [h6084, h6169, hlam]
                                                · linarith only [h6063, h6169, hlam]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [h5135, h6066, h6088, h6103, hc23, hc45, hlam, hphi, ht34, p6136_1]
                                              · have p6136_0 := h6136c.1
                                                have p6136_1 := h6136c.2.1
                                                have p6136_2 := h6136c.2.2.1
                                                have p6136_3 := h6136c.2.2.2
                                                linarith only [hlam, p6136_0]
                                      · linarith only [h6090, h6129, hlam]
                                    · linarith only [h6128, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6105_1]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    rcases p6105_3 (m.d 0 2) (by simp) with h6178 | h6178
                                    · linarith only [h0, h6178, hlam]
                                    · linarith only [h6063, h6178, hlam]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    rcases p6105_3 (m.d 0 2) (by simp) with h6181 | h6181
                                    · linarith only [h0, h6181, hlam]
                                    · linarith only [h6064, h6181, hlam]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    rcases p6105_3 (m.d 0 2) (by simp) with h6184 | h6184
                                    · linarith only [h0, h6184, hlam]
                                    · linarith only [h6065, h6184, hlam]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6063, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6088, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6097, hlam, p6105_1]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6099, hlam, p6105_1]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6064, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6089, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h5136, h6089, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6105_1]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6101, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6065, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6090, hlam, p6105_0]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h6065, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6105_1]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [h0, h6065, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6105_1]
                                  · have p6105_0 := h6105c.1
                                    have p6105_1 := h6105c.2.1
                                    have p6105_2 := h6105c.2.2.1
                                    have p6105_3 := h6105c.2.2.2
                                    linarith only [hlam, p6105_0]
                  · linarith only [h0, h6065, h6090, hlam]
                · linarith only [h0, h6064, h6089, hlam]
              · linarith only [h0, h5135, h6063, h6088, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h6205 | h6205
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6206 | h6206
          · linarith only [h0, h5135, h6065, h6206, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6208 | h6208
            · linarith only [h0, h5135, h6065, h6205, h6208, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6210 | h6210
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6211 | h6211
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6212 | h6212
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6213 | h6213
                    · linarith only [h0, h5135, h6065, h6212, h6213, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h5135, h6065, h6205, h6210, h6212, h6213, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6216 | h6216
                    · linarith only [h0, h5135, h6212, h6216, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h5135, h6205, h6210, h6212, h6216, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h6064, h6211, hlam]
              · linarith only [h0, h6063, h6210, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h6221 | h6221
          · linarith only [h5136, h5137, h6205, h6221, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h6223 | h6223
            · linarith only [h0, h5136, h6065, h6223, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h6225 | h6225
              · rcases m.htr 1 2 4 (by decide) (by decide) with h6226 | h6226
                · rcases m.htr 1 2 5 (by decide) (by decide) with h6227 | h6227
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6228 | h6228
                    · linarith only [h0, h5135, h6065, h6205, h6227, h6228, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6230 | h6230
                      · linarith only [h0, h5135, h6065, h6221, h6230, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6232 | h6232
                        · linarith only [h0, h5136, h6065, h6223, h6227, h6232, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6234 | h6234
                          · linarith only [h5135, h6205, h6225, h6234, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6236 | h6236
                            · linarith only [h0, h5136, h6065, h6225, h6227, h6228, h6236, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6238 | h6238
                              · linarith only [h0, h5136, h6065, h6226, h6227, h6232, h6238, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6240 | h6240
                                · linarith only [h0, h5136, h6065, h6225, h6227, h6228, h6232, h6240, hc23, hc34, hlam, hphi]
                                · rcases h2bigk with h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c | h6242c
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h0, hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6065, h6227, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6065, h6227, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6065, hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    rcases p6242_3 (m.d 0 2) (by simp) with h6250 | h6250
                                    · linarith only [h0, h6250, hlam]
                                    · linarith only [h6063, h6250, hlam]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    rcases p6242_3 (m.d 0 2) (by simp) with h6253 | h6253
                                    · linarith only [h0, h6253, hlam]
                                    · linarith only [h6064, h6253, hlam]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h0, h5136, h6065, h6225, h6228, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6063, hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6225, hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6234, hlam, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6236, hlam, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6064, hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6226, hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6064, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6238, hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [hc02, hc25, hlam, hphi, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6227, hlam, p6242_0]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6227, h6230, hc23, hc35, hlam, hphi, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [h6227, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6242_1]
                                  · have p6242_0 := h6242c.1
                                    have p6242_1 := h6242c.2.1
                                    have p6242_2 := h6242c.2.2.1
                                    have p6242_3 := h6242c.2.2.2
                                    linarith only [hlam, p6242_0]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h6272 | h6272
                    · linarith only [h5135, h6205, h6272, hlam]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h6274 | h6274
                      · linarith only [h0, h5135, h6227, h6274, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h6276 | h6276
                        · linarith only [h0, h5136, h6227, h6276, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6278 | h6278
                          · linarith only [h0, h5136, h6205, h6225, h6227, h6272, h6278, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6280 | h6280
                            · linarith only [h0, h5136, h6225, h6227, h6272, h6274, h6280, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h5136, h6227, h6272, h6280, hc13, hc35, hlam, hphi]
                · linarith only [h0, h5135, h6064, h6225, h6226, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h5135, h6063, h6225, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h5136, h6064, hlam]
  · linarith only [h0, h5135, h6063, hlam]

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h5137 | h5137
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x0 m hb2 hb3 hb5 hg0 h5135 h5136 h5137
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0_x1 m hb2 hb3 hb5 hg0 h5135 h5136 h5137

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5136 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h6287 | h6287
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6288 | h6288
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6289 | h6289
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6290 | h6290
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6291 | h6291
          · linarith only [h5135, h5136, h6291, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6293 | h6293
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6294 | h6294
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6295 | h6295
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6296 | h6296
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6297 | h6297
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6298 | h6298
                      · linarith only [h5135, h5136, h6291, h6298, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6300 | h6300
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6301 | h6301
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6302 | h6302
                            · linarith only [h5135, h5136, h6298, h6300, h6302, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6304 | h6304
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6305 | h6305
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6306 | h6306
                                  · rcases h2bigk with h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c | h6307c
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h0, hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6304, h6306, hc02, hc45, hlam, hphi, ht0b, ht5b, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h0, h6302, h6304, h6306, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      rcases p6307_3 (m.d 0 2) (by simp) with h6312 | h6312
                                      · rcases p6307_3 (m.d 1 2) (by simp) with h6313 | h6313
                                        · rcases p6307_3 (m.d 2 3) (by simp) with h6314 | h6314
                                          · linarith only [h6288, h6314, hlam]
                                          · linarith only [h6304, h6314, hlam]
                                        · linarith only [h6297, h6313, hlam]
                                      · linarith only [h6312, hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h0, h5135, h6295, h6304, h6306, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6304, h6306, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6302, h6304, h6306, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      rcases p6307_3 (m.d 0 2) (by simp) with h6323 | h6323
                                      · linarith only [h0, h6323, hlam]
                                      · linarith only [h6290, h6323, hlam]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6288, hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6295, hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6302, hlam, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h5135, h6295, h6304, h6306, hc01, hc45, hlam, hphi, ht0b, ht5b, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6289, hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6296, hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6289, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h0, h6289, h6304, h6306, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6290, hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6297, hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6304, hlam, p6307_0]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [h6305, hlam, p6307_1]
                                    · have p6307_0 := h6307c.1
                                      have p6307_1 := h6307c.2.1
                                      have p6307_2 := h6307c.2.2.1
                                      have p6307_3 := h6307c.2.2.2
                                      linarith only [hlam, p6307_0]
                                  · linarith only [h5135, h5136, h6295, h6298, h6304, h6306, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h5135, h5136, h6300, h6301, h6302, h6304, h6305, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h5135, h5136, h6293, h6298, h6304, hc23, hc34, hlam, hphi]
                          · linarith only [h5135, h5136, h6301, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h5135, h5136, h6293, h6298, h6300, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h6290, h6297, hlam]
                  · linarith only [h0, h6289, h6296, hlam]
                · linarith only [h0, h6288, h6295, hlam]
              · linarith only [h5136, h6287, h6294, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6350 | h6350
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6351 | h6351
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6352 | h6352
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6353 | h6353
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6354 | h6354
                      · linarith only [h5135, h5136, h6291, h6352, h6354, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6356 | h6356
                        · linarith only [h5135, h6293, h6356, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6358 | h6358
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6359 | h6359
                            · linarith only [h5136, h6287, h6288, h6354, h6356, h6359, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6361 | h6361
                              · linarith only [h5135, h6293, h6351, h6361, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6363 | h6363
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6364 | h6364
                                  · rcases h2bigk with h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c | h6365c
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h0, hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      rcases p6365_3 (m.d 0 2) (by simp) with h6368 | h6368
                                      · rcases p6365_3 (m.d 1 2) (by simp) with h6369 | h6369
                                        · rcases p6365_3 (m.d 2 3) (by simp) with h6370 | h6370
                                          · linarith only [h6370, hlam, p6365_0]
                                          · rcases p6365_3 (m.d 2 4) (by simp) with h6372 | h6372
                                            · linarith only [h6289, h6372, hlam]
                                            · linarith only [h6359, h6372, hlam]
                                        · linarith only [h6351, h6369, hlam]
                                      · linarith only [h6368, hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h0, h6363, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6365_1]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      rcases p6365_3 (m.d 0 2) (by simp) with h6378 | h6378
                                      · rcases p6365_3 (m.d 1 2) (by simp) with h6379 | h6379
                                        · rcases p6365_3 (m.d 2 3) (by simp) with h6380 | h6380
                                          · linarith only [h6288, h6380, hlam]
                                          · rcases p6365_3 (m.d 2 4) (by simp) with h6382 | h6382
                                            · linarith only [h6289, h6382, hlam]
                                            · linarith only [h6363, h6382, hlam]
                                        · linarith only [h6353, h6379, hlam]
                                      · linarith only [h6378, hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h0, h6287, h6351, h6356, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6365_1]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      rcases p6365_3 (m.d 0 2) (by simp) with h6389 | h6389
                                      · linarith only [h0, h6389, hlam]
                                      · linarith only [h6288, h6389, hlam]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6363, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6365_1]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      rcases p6365_3 (m.d 0 2) (by simp) with h6393 | h6393
                                      · linarith only [h0, h6393, hlam]
                                      · linarith only [h6290, h6393, hlam]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6288, hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6351, hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6359, hlam, p6365_1]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6361, hlam, p6365_1]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6289, hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6352, hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6289, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6365_1]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h5136, h6289, h6354, h6361, hc23, hc34, hlam, hphi, p6365_1]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6290, hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6353, hlam, p6365_0]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h0, h6290, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6365_1]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [h6363, hlam, p6365_1]
                                    · have p6365_0 := h6365c.1
                                      have p6365_1 := h6365c.2.1
                                      have p6365_2 := h6365c.2.2.1
                                      have p6365_3 := h6365c.2.2.2
                                      linarith only [hlam, p6365_0]
                                  · linarith only [h5135, h5136, h6351, h6354, h6364, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h5136, h6287, h6354, h6358, h6359, h6363, hc23, hc34, hlam, hphi]
                          · linarith only [h5136, h6287, h6356, h6358, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6290, h6353, hlam]
                  · linarith only [h0, h6289, h6352, hlam]
                · linarith only [h0, h6287, h6288, h6351, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h5136, h6287, h6350, hlam]
        · linarith only [h0, h6287, h6290, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6419 | h6419
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6420 | h6420
          · linarith only [h0, h5135, h6289, h6420, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6422 | h6422
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6423 | h6423
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6424 | h6424
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6425 | h6425
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6426 | h6426
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6427 | h6427
                      · linarith only [h0, h5135, h6289, h6420, h6425, h6427, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6429 | h6429
                        · linarith only [h0, h5135, h6289, h6425, h6429, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h5135, h6289, h6422, h6424, h6425, h6429, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6289, h6425, h6426, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6433 | h6433
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6434 | h6434
                      · linarith only [h0, h5135, h6425, h6434, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6436 | h6436
                        · linarith only [h0, h5135, h6425, h6436, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h5135, h6422, h6424, h6425, h6436, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h6287, h6289, h6419, h6433, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6288, h6424, hlam]
              · linarith only [h0, h5135, h6289, h6422, h6423, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6442 | h6442
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6443 | h6443
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6444 | h6444
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6445 | h6445
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6446 | h6446
                      · linarith only [h0, h5135, h6289, h6444, h6446, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6448 | h6448
                        · linarith only [h0, h5135, h6289, h6422, h6444, h6448, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6450 | h6450
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6451 | h6451
                            · linarith only [h0, h6287, h6289, h6443, h6444, h6446, h6448, h6451, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6453 | h6453
                              · linarith only [h5135, h6422, h6443, h6453, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6455 | h6455
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6456 | h6456
                                  · rcases h2bigk with h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h0, hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6289, h6444, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6289, hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6289, h6444, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      rcases p6457_3 (m.d 0 2) (by simp) with h6465 | h6465
                                      · linarith only [h0, h6465, hlam]
                                      · linarith only [h6288, h6465, hlam]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h0, h6287, h6289, h6443, h6448, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      rcases p6457_3 (m.d 0 2) (by simp) with h6469 | h6469
                                      · linarith only [h0, h6469, hlam]
                                      · linarith only [h6419, h6469, hlam]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6288, hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6443, hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6451, hlam, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6453, hlam, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h0, h6287, h6443, h6444, h6448, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6444, hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6444, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6444, h6453, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6419, hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6445, hlam, p6457_0]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6419, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [h6455, hlam, p6457_1]
                                    · have p6457_0 := h6457c.1
                                      have p6457_1 := h6457c.2.1
                                      have p6457_2 := h6457c.2.2.1
                                      have p6457_3 := h6457c.2.2.2
                                      linarith only [hlam, p6457_0]
                                  · linarith only [h5136, h6287, h6443, h6446, h6448, h6456, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h0, h6287, h6289, h6450, h6455, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                          · linarith only [h0, h6287, h6289, h6442, h6444, h6450, hlam]
                    · linarith only [h6289, h6419, h6445, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6491 | h6491
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6492 | h6492
                      · linarith only [h0, h5135, h6420, h6444, h6492, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6494 | h6494
                        · linarith only [h0, h5135, h6444, h6494, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6496 | h6496
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6497 | h6497
                            · linarith only [h0, h6287, h6443, h6444, h6492, h6494, h6497, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h6287, h6443, h6444, h6494, h6497, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h6287, h6443, h6444, h6494, h6496, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6287, h6289, h6419, h6491, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6288, h6443, hlam]
              · linarith only [h0, h6287, h6289, h6442, hlam]
        · linarith only [h0, h6287, h6419, hlam]
    · linarith only [h0, h5135, h6288, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6506 | h6506
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6507 | h6507
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6508 | h6508
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6509 | h6509
          · linarith only [h5135, h5136, h6509, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6511 | h6511
            · linarith only [h5135, h6287, h6511, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6513 | h6513
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6514 | h6514
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6515 | h6515
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6516 | h6516
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6517 | h6517
                      · linarith only [h5135, h5136, h6509, h6515, h6517, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6519 | h6519
                        · linarith only [h5135, h6287, h6511, h6519, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6521 | h6521
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6522 | h6522
                            · linarith only [h5135, h6287, h6506, h6517, h6521, h6522, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6524 | h6524
                              · linarith only [h5135, h6287, h6514, h6519, h6524, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6526 | h6526
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6527 | h6527
                                  · rcases h2bigk with h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c | h6528c
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h0, hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      rcases p6528_3 (m.d 0 2) (by simp) with h6531 | h6531
                                      · rcases p6528_3 (m.d 1 2) (by simp) with h6532 | h6532
                                        · rcases p6528_3 (m.d 2 3) (by simp) with h6533 | h6533
                                          · linarith only [h6533, hlam, p6528_0]
                                          · rcases p6528_3 (m.d 2 4) (by simp) with h6535 | h6535
                                            · linarith only [h6507, h6535, hlam]
                                            · linarith only [h6522, h6535, hlam]
                                        · linarith only [h6514, h6532, hlam]
                                      · linarith only [h6531, hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h0, h6526, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6528_1]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      rcases p6528_3 (m.d 0 2) (by simp) with h6541 | h6541
                                      · rcases p6528_3 (m.d 1 2) (by simp) with h6542 | h6542
                                        · rcases p6528_3 (m.d 2 3) (by simp) with h6543 | h6543
                                          · linarith only [h6506, h6543, hlam]
                                          · rcases p6528_3 (m.d 2 4) (by simp) with h6545 | h6545
                                            · linarith only [h6507, h6545, hlam]
                                            · linarith only [h6526, h6545, hlam]
                                        · linarith only [h6516, h6542, hlam]
                                      · linarith only [h6541, hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h0, h5135, h6514, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6528_1]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      rcases p6528_3 (m.d 0 2) (by simp) with h6552 | h6552
                                      · linarith only [h0, h6552, hlam]
                                      · linarith only [h6506, h6552, hlam]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6526, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6528_1]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      rcases p6528_3 (m.d 0 2) (by simp) with h6556 | h6556
                                      · linarith only [h0, h6556, hlam]
                                      · linarith only [h6508, h6556, hlam]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6506, hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6514, hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6522, hlam, p6528_1]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6524, hlam, p6528_1]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6507, hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6515, hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6507, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6528_1]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h5136, h6507, h6517, h6524, hc23, hc34, hlam, hphi, p6528_1]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6508, hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6516, hlam, p6528_0]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h0, h6508, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6528_1]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [h6526, hlam, p6528_1]
                                    · have p6528_0 := h6528c.1
                                      have p6528_1 := h6528c.2.1
                                      have p6528_2 := h6528c.2.2.1
                                      have p6528_3 := h6528c.2.2.2
                                      linarith only [hlam, p6528_0]
                                  · linarith only [h5135, h5136, h6514, h6517, h6527, hc23, hc45, hlam, hphi, ht34]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6575 | h6575
                                  · rcases h2bigk with h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c | h6576c
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h0, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      rcases p6576_3 (m.d 0 2) (by simp) with h6579 | h6579
                                      · rcases p6576_3 (m.d 1 2) (by simp) with h6580 | h6580
                                        · rcases p6576_3 (m.d 2 3) (by simp) with h6581 | h6581
                                          · linarith only [h6581, hlam, p6576_0]
                                          · rcases p6576_3 (m.d 2 4) (by simp) with h6583 | h6583
                                            · linarith only [h6507, h6583, hlam]
                                            · linarith only [h6522, h6583, hlam]
                                        · linarith only [h6514, h6580, hlam]
                                      · linarith only [h6579, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      rcases p6576_3 (m.d 0 2) (by simp) with h6588 | h6588
                                      · rcases p6576_3 (m.d 1 2) (by simp) with h6589 | h6589
                                        · rcases p6576_3 (m.d 2 3) (by simp) with h6590 | h6590
                                          · linarith only [h6506, h6590, hlam]
                                          · rcases p6576_3 (m.d 2 4) (by simp) with h6592 | h6592
                                            · linarith only [h6592, hlam, p6576_0]
                                            · rcases p6576_3 (m.d 2 5) (by simp) with h6594 | h6594
                                              · linarith only [h6508, h6594, hlam]
                                              · linarith only [h6526, h6594, hlam]
                                        · linarith only [h6515, h6589, hlam]
                                      · linarith only [h6588, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      rcases p6576_3 (m.d 0 2) (by simp) with h6599 | h6599
                                      · rcases p6576_3 (m.d 1 2) (by simp) with h6600 | h6600
                                        · rcases p6576_3 (m.d 2 3) (by simp) with h6601 | h6601
                                          · linarith only [h6506, h6601, hlam]
                                          · rcases p6576_3 (m.d 2 4) (by simp) with h6603 | h6603
                                            · linarith only [h6507, h6603, hlam]
                                            · rcases p6576_3 (m.d 2 5) (by simp) with h6605 | h6605
                                              · linarith only [h6605, hlam, p6576_0]
                                              · rcases h3bigk with h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c | h6607c
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h5135, h6287, h6514, h6519, hc23, hc35, hlam, hphi, p6607_1]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h5135, h6287, h6519, hc23, hc35, hlam, hphi, p6607_1]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6509, hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6511, hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h5135, hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h5135, h6287, h6519, hc23, hc35, hlam, hphi, p6607_1]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6517, hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6519, hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6506, hlam, p6607_1]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6514, hlam, p6607_1]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6522, hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6524, hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  rcases p6607_3 (m.d 0 3) (by simp) with h6623 | h6623
                                                  · linarith only [h6623, hlam, p6607_0]
                                                  · rcases p6607_3 (m.d 1 3) (by simp) with h6625 | h6625
                                                    · linarith only [h6517, h6625, hlam]
                                                    · rcases p6607_3 (m.d 2 3) (by simp) with h6627 | h6627
                                                      · linarith only [h6522, h6627, hlam]
                                                      · rcases p6607_3 (m.d 3 4) (by simp) with h6629 | h6629
                                                        · rcases p6607_3 (m.d 3 5) (by simp) with h6630 | h6630
                                                          · linarith only [h6575, h6630, hlam]
                                                          · linarith only [h6511, h6630, hlam]
                                                        · linarith only [h6629, hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  rcases p6607_3 (m.d 0 3) (by simp) with h6634 | h6634
                                                  · linarith only [h6509, h6634, hlam]
                                                  · linarith only [h5135, h6634, hlam]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  rcases p6607_3 (m.d 0 3) (by simp) with h6637 | h6637
                                                  · linarith only [h6509, h6637, hlam]
                                                  · linarith only [h6506, h6637, hlam]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [hlam, p6607_0]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6511, hc03, hc34, hlam, hphi, p6607_1]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  rcases p6607_3 (m.d 0 3) (by simp) with h6642 | h6642
                                                  · linarith only [h6642, hlam, p6607_0]
                                                  · rcases p6607_3 (m.d 1 3) (by simp) with h6644 | h6644
                                                    · linarith only [h6519, h6644, hlam]
                                                    · rcases p6607_3 (m.d 2 3) (by simp) with h6646 | h6646
                                                      · linarith only [h6524, h6646, hlam]
                                                      · rcases p6607_3 (m.d 3 4) (by simp) with h6648 | h6648
                                                        · rcases p6607_3 (m.d 3 5) (by simp) with h6649 | h6649
                                                          · rcases h5bigk with h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c | h6650c
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [hlam, p6650_0]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6287, hlam, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              rcases p6650_3 (m.d 0 5) (by simp) with h6653 | h6653
                                                              · rcases p6650_3 (m.d 1 5) (by simp) with h6654 | h6654
                                                                · rcases p6650_3 (m.d 2 5) (by simp) with h6655 | h6655
                                                                  · linarith only [h6508, h6655, hlam]
                                                                  · rcases p6650_3 (m.d 3 5) (by simp) with h6657 | h6657
                                                                    · rcases p6650_3 (m.d 4 5) (by simp) with h6658 | h6658
                                                                      · linarith only [h6513, h6658, hlam]
                                                                      · linarith only [h6526, h6658, hlam]
                                                                    · linarith only [h6524, h6657, hlam]
                                                                · linarith only [h6516, h6654, hlam]
                                                              · linarith only [h6508, h6653, hlam]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6511, hlam, p6650_0]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6287, h6517, h6521, h6522, h6526, hc23, hc34, hlam, hphi, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h5135, h6287, h6514, h6517, h6521, hc23, hc34, hlam, hphi, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [hlam, p6650_0]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              rcases p6650_3 (m.d 0 5) (by simp) with h6668 | h6668
                                                              · linarith only [h6287, h6668, hlam]
                                                              · linarith only [h6508, h6668, hlam]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6519, hlam, p6650_0]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6517, h6521, h6522, h6526, hc23, hc34, hlam, hphi, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6508, hlam, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6516, hlam, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [hlam, p6650_0]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6524, hlam, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6526, hlam, p6650_0]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h5135, h6287, h6514, hc23, hc35, hlam, hphi, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h5135, h6287, h6514, hc23, hc35, hlam, hphi, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              rcases p6650_3 (m.d 0 5) (by simp) with h6680 | h6680
                                                              · linarith only [h6511, h6680, hlam]
                                                              · linarith only [h6508, h6680, hlam]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [hlam, p6650_0]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6522, h6526, h6575, hc23, hc34, hlam, hphi, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6513, hlam, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6521, hlam, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h5136, h6513, h6517, h6522, h6526, hc23, hc34, hlam, hphi, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [h6575, hlam, p6650_1]
                                                            · have p6650_0 := h6650c.1
                                                              have p6650_1 := h6650c.2.1
                                                              have p6650_2 := h6650c.2.2.1
                                                              have p6650_3 := h6650c.2.2.2
                                                              linarith only [hlam, p6650_0]
                                                          · linarith only [h6649, hlam, p6607_0]
                                                        · linarith only [h6509, h6648, hlam]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  rcases p6607_3 (m.d 0 3) (by simp) with h6692 | h6692
                                                  · linarith only [h6511, h6692, hlam]
                                                  · linarith only [h5135, h6692, hlam]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  rcases p6607_3 (m.d 0 3) (by simp) with h6695 | h6695
                                                  · linarith only [h6511, h6695, hlam]
                                                  · linarith only [h6506, h6695, hlam]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [h6575, hlam, p6607_1]
                                                · have p6607_0 := h6607c.1
                                                  have p6607_1 := h6607c.2.1
                                                  have p6607_2 := h6607c.2.2.1
                                                  have p6607_3 := h6607c.2.2.2
                                                  linarith only [hlam, p6607_0]
                                        · linarith only [h6516, h6600, hlam]
                                      · linarith only [h6599, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h0, h5135, h6514, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6576_1]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      rcases p6576_3 (m.d 0 2) (by simp) with h6704 | h6704
                                      · linarith only [h0, h6704, hlam]
                                      · linarith only [h6506, h6704, hlam]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      rcases p6576_3 (m.d 0 2) (by simp) with h6707 | h6707
                                      · linarith only [h0, h6707, hlam]
                                      · linarith only [h6507, h6707, hlam]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      rcases p6576_3 (m.d 0 2) (by simp) with h6710 | h6710
                                      · linarith only [h0, h6710, hlam]
                                      · linarith only [h6508, h6710, hlam]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6506, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6514, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6522, hlam, p6576_1]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6524, hlam, p6576_1]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6507, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6515, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6507, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6576_1]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6526, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6508, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h6516, hlam, p6576_0]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h0, h6508, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6576_1]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [h0, h6508, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6576_1]
                                    · have p6576_0 := h6576c.1
                                      have p6576_1 := h6576c.2.1
                                      have p6576_2 := h6576c.2.2.1
                                      have p6576_3 := h6576c.2.2.2
                                      linarith only [hlam, p6576_0]
                                  · linarith only [h5136, h6513, h6517, h6575, hlam]
                          · linarith only [h5136, h6513, h6521, hlam]
                    · linarith only [h0, h6508, h6516, hlam]
                  · linarith only [h0, h6507, h6515, hlam]
                · linarith only [h0, h6506, h6514, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6733 | h6733
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6734 | h6734
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6735 | h6735
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6736 | h6736
                      · linarith only [h5135, h5136, h6509, h6736, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6738 | h6738
                        · linarith only [h5135, h5136, h6511, h6513, h6738, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6740 | h6740
                          · linarith only [h5135, h5136, h6513, h6736, h6740, hc13, hc34, hlam, hphi]
                          · linarith only [h5135, h5136, h6733, h6740, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h5135, h5136, h6508, h6733, h6734, h6735, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h6507, h6734, hlam]
                · linarith only [h0, h6506, h6733, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6746 | h6746
          · linarith only [h5135, h5136, h6746, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6748 | h6748
            · linarith only [h0, h5135, h6508, h6748, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6750 | h6750
              · linarith only [h6507, h6508, h6750, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6752 | h6752
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6753 | h6753
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6754 | h6754
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6755 | h6755
                      · linarith only [h5135, h5136, h6507, h6508, h6746, h6754, h6755, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6757 | h6757
                        · linarith only [h5135, h5136, h6507, h6508, h6748, h6757, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6759 | h6759
                          · linarith only [h5135, h5136, h6750, h6755, h6759, hc13, hc34, hlam, hphi]
                          · linarith only [h5135, h5136, h6752, h6759, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6762 | h6762
                      · linarith only [h0, h5135, h6754, h6762, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6764 | h6764
                        · linarith only [h5135, h5136, h6753, h6754, h6764, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6766 | h6766
                          · linarith only [h5135, h5136, h6750, h6752, h6753, h6754, h6766, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h5135, h5136, h6752, h6766, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h5135, h6507, h6752, h6753, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6506, h6752, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6771 | h6771
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6772 | h6772
          · linarith only [h0, h5135, h6507, h6772, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6774 | h6774
            · linarith only [h5135, h6287, h6774, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6776 | h6776
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6777 | h6777
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6778 | h6778
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6779 | h6779
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6780 | h6780
                      · linarith only [h5135, h6287, h6507, h6771, h6772, h6778, h6780, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6782 | h6782
                        · linarith only [h5135, h6287, h6774, h6782, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6784 | h6784
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6785 | h6785
                            · linarith only [h6506, h6507, h6778, h6780, h6785, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6787 | h6787
                              · linarith only [h5135, h6287, h6507, h6771, h6777, h6778, h6787, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6789 | h6789
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6790 | h6790
                                  · rcases h2bigk with h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c | h6791c
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h0, hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6507, h6778, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6507, hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6507, h6778, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6287, h6771, hc01, hc12, hlam, hphi, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      rcases p6791_3 (m.d 0 2) (by simp) with h6799 | h6799
                                      · linarith only [h0, h6799, hlam]
                                      · linarith only [h6506, h6799, hlam]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h5135, h6287, h6507, h6771, h6777, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      rcases p6791_3 (m.d 0 2) (by simp) with h6803 | h6803
                                      · linarith only [h0, h6803, hlam]
                                      · linarith only [h6771, h6803, hlam]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6506, hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6777, hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6785, hlam, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6787, hlam, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h5135, h6287, h6771, h6777, h6778, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6778, hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6778, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6778, h6787, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6771, hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6779, hlam, p6791_0]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6771, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [h6789, hlam, p6791_1]
                                    · have p6791_0 := h6791c.1
                                      have p6791_1 := h6791c.2.1
                                      have p6791_2 := h6791c.2.2.1
                                      have p6791_3 := h6791c.2.2.2
                                      linarith only [hlam, p6791_0]
                                  · linarith only [h5135, h5136, h6777, h6780, h6790, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h6507, h6771, h6776, h6789, hlam]
                          · linarith only [h6507, h6771, h6776, h6778, h6784, hlam]
                    · linarith only [h6507, h6771, h6779, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6825 | h6825
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6826 | h6826
                      · linarith only [h5135, h6287, h6778, h6825, h6826, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6828 | h6828
                        · linarith only [h5135, h6287, h6778, h6825, h6828, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6830 | h6830
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6831 | h6831
                            · linarith only [h5135, h6287, h6777, h6778, h6825, h6826, h6831, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h5135, h6287, h6777, h6778, h6825, h6831, hc23, hc34, hlam, hphi]
                          · linarith only [h5135, h5136, h6777, h6830, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h5135, h6771, h6777, h6825, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6506, h6777, hlam]
              · linarith only [h6507, h6771, h6776, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6838 | h6838
          · linarith only [h0, h5135, h6507, h6838, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6840 | h6840
            · linarith only [h0, h5135, h6771, h6840, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6842 | h6842
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6843 | h6843
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6844 | h6844
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6845 | h6845
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6846 | h6846
                      · linarith only [h0, h5135, h6507, h6838, h6844, h6846, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6848 | h6848
                        · linarith only [h0, h5135, h6771, h6840, h6848, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6850 | h6850
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6851 | h6851
                            · linarith only [h5136, h6506, h6507, h6844, h6846, h6851, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6853 | h6853
                              · linarith only [h0, h5135, h6771, h6843, h6845, h6848, h6853, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6855 | h6855
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6856 | h6856
                                  · rcases h2bigk with h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c | h6857c
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h0, hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6771, h6845, h6850, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6507, hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6771, hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      rcases p6857_3 (m.d 0 2) (by simp) with h6865 | h6865
                                      · linarith only [h0, h6865, hlam]
                                      · linarith only [h6506, h6865, hlam]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h0, h5135, h6771, h6843, h6855, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h0, h5135, h6771, h6843, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6506, hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6843, hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6851, hlam, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6853, hlam, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h0, h5135, h6843, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6844, hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6844, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h0, h5135, h6771, h6843, h6844, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h0, h5135, h6843, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6845, hlam, p6857_0]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6845, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [h6855, hlam, p6857_1]
                                    · have p6857_0 := h6857c.1
                                      have p6857_1 := h6857c.2.1
                                      have p6857_2 := h6857c.2.2.1
                                      have p6857_3 := h6857c.2.2.2
                                      linarith only [hlam, p6857_0]
                                  · linarith only [h5135, h5136, h6843, h6846, h6856, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h0, h5135, h6507, h6842, h6843, h6855, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · linarith only [h5135, h5136, h6842, h6843, h6850, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h5135, h6507, h6843, h6844, h6845, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6889 | h6889
                    · linarith only [h0, h5135, h6771, h6843, h6844, h6889, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6891 | h6891
                      · linarith only [h0, h5135, h6838, h6844, h6891, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6893 | h6893
                        · linarith only [h0, h5135, h6844, h6893, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6895 | h6895
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6896 | h6896
                            · linarith only [h0, h5135, h5136, h6843, h6844, h6891, h6896, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h5135, h6843, h6844, h6896, hc23, hc34, hlam, hphi]
                          · linarith only [h5135, h5136, h6843, h6895, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h5135, h6506, h6771, h6842, h6843, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6901 | h6901
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6902 | h6902
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6903 | h6903
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6904 | h6904
                      · linarith only [h0, h5135, h6507, h6902, h6904, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6906 | h6906
                        · linarith only [h0, h5135, h6507, h6902, h6906, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6908 | h6908
                          · linarith only [h5135, h5136, h6842, h6904, h6908, hc13, hc34, hlam, hphi]
                          · linarith only [h5135, h5136, h6901, h6908, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h5135, h6507, h6901, h6902, h6903, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6912 | h6912
                    · linarith only [h0, h5135, h6771, h6901, h6902, h6912, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6914 | h6914
                      · linarith only [h0, h5135, h6902, h6914, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6916 | h6916
                        · linarith only [h0, h5135, h6902, h6916, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6918 | h6918
                          · linarith only [h0, h5135, h6507, h6842, h6901, h6914, h6918, hc23, hc34, hlam, hphi]
                          · linarith only [h5135, h5136, h6901, h6918, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h5135, h6506, h6901, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h5135, h6506, hlam]

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h5136 | h5136
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x0 m hb2 hb3 hb5 hg0 h5135 h5136
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0_x1 m hb2 hb3 hb5 hg0 h5135 h5136

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  exact r1l7_22_13_15_H_I_L_I_L_I_s6 m hb2 hb3 hb5 h0 h5135

set_option maxHeartbeats 14576000 in
set_option maxHeartbeats 14576000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s5 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h5135 | h5135
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x0 m hb2 hb3 hb5 hg0 h5135
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5_x1 m hb2 hb3 hb5 hg0 h5135

set_option maxHeartbeats 24846000 in
set_option maxHeartbeats 24846000 in
theorem r1l7_22_13_15_H_I_L_I_L_I (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have hc05 := m.hcor 0 5 (by decide)
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_H_I_L_I_L_I_s0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_H_I_L_I_L_I_s5 m hb2 hb3 hb5 h0

end R2N4
