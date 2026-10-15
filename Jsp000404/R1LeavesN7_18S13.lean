import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8273 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 2 5 (by decide) (by decide) with h9095 | h9095
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9096 | h9096
    · linarith only [h8272, h8273, h9096, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9098 | h9098
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9099 | h9099
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9100 | h9100
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9101 | h9101
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9102 | h9102
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9103 | h9103
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9104 | h9104
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9105 | h9105
                    · linarith only [h8272, h8273, h9096, h9101, h9105, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9107 | h9107
                      · linarith only [h8272, h8273, h9100, h9103, h9105, h9107, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h8272, h8273, h9098, h9100, h9103, h9105, h9107, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h8272, h8273, h9098, h9103, h9104, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9111 | h9111
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9112 | h9112
                    · linarith only [h8272, h8273, h9101, h9103, h9112, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9114 | h9114
                      · linarith only [h8272, h8273, h9101, h9114, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h8272, h8273, h9098, h9101, h9114, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h8272, h8273, h9098, h9101, h9111, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h8273, h9095, h9101, h9102, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9119 | h9119
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9120 | h9120
                · linarith only [h9096, h9098, h9100, h9101, h9120, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9122 | h9122
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9123 | h9123
                    · linarith only [h7594, h9120, h9122, h9123, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9125 | h9125
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9126 | h9126
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9127 | h9127
                          · rcases h0bigk with h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c | h9128c
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [hlam, p9128_0]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h0, hlam, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h5743, hlam, p9128_0]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h6852, hlam, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h7594, hlam, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h0, h9101, h9123, hc01, hc34, hlam, hphi, ht12, ht23, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [hlam, p9128_0]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h0, h9101, h9123, hc03, hc34, hlam, hphi, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h8273, hlam, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h0, h7594, h9101, h9123, hc01, hc34, hlam, hphi, ht12, ht23, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h5743, hc01, hc13, hlam, hphi, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h8272, hlam, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [hlam, p9128_0]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h9096, hlam, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h0, h7594, h8272, h9101, h9123, hc01, hc34, hlam, hphi, ht12, ht23, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h6852, h9101, h9123, hc01, hc34, hlam, hphi, ht12, ht23, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h6852, h8272, h9101, h9123, h9125, h9127, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h6852, h9101, h9123, hc03, hc34, hlam, hphi, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [hlam, p9128_0]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h6852, h7594, h9101, h9123, hc01, hc34, hlam, hphi, ht12, ht23, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h9095, hlam, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h9098, hlam, p9128_0]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [h9099, hlam, p9128_1]
                            · have p9128_0 := h9128c.1
                              have p9128_1 := h9128c.2.1
                              have p9128_2 := h9128c.2.2.1
                              have p9128_3 := h9128c.2.2.2
                              linarith only [hlam, p9128_0]
                          · linarith only [h0, h9101, h9123, h9127, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h8272, h9098, h9099, h9101, h9125, h9126, hc03, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h5743, h9098, h9100, h9101, h9123, h9125, hc23, hc34, hlam, hphi]
                  · linarith only [h5743, h9098, h9122, hlam]
              · linarith only [h0, h9095, h9119, hlam]
          · linarith only [h0, h8272, h9100, hlam]
        · linarith only [h8272, h8273, h9098, h9099, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9161 | h9161
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9162 | h9162
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9163 | h9163
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9164 | h9164
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9165 | h9165
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9166 | h9166
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9167 | h9167
                    · linarith only [h5743, h8272, h8273, h9096, h9163, h9167, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9169 | h9169
                      · linarith only [h5743, h8272, h8273, h9098, h9162, h9165, h9167, h9169, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9171 | h9171
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9172 | h9172
                          · rcases h0bigk with h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c | h9173c
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [hlam, p9173_0]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h0, hlam, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h5743, hlam, p9173_0]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h6852, hlam, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h7594, hlam, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h8273, h9162, h9165, h9167, hc01, hc12, hlam, hphi, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [hlam, p9173_0]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h5743, h8273, h9162, h9165, h9167, hc01, hc12, hlam, hphi, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h8273, hlam, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h8273, h9162, h9165, h9167, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h9098, h9166, hc01, hc15, hlam, hphi, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h8272, hlam, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [hlam, p9173_0]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h9096, hlam, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h9098, hlam, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h6852, hc01, hc14, hlam, hphi, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h8273, h9095, h9162, h9165, h9167, h9169, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h8273, h9162, h9165, h9167, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [hlam, p9173_0]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h5743, h8273, h9098, h9162, h9165, h9167, hc01, hc12, hlam, hphi, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h9095, hlam, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h5743, h8273, h9095, h9162, h9165, h9167, hc01, hc12, hlam, hphi, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [h9161, hlam, p9173_1]
                            · have p9173_0 := h9173c.1
                              have p9173_1 := h9173c.2.1
                              have p9173_2 := h9173c.2.2.1
                              have p9173_3 := h9173c.2.2.2
                              linarith only [hlam, p9173_0]
                          · linarith only [h8272, h8273, h9167, h9172, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h8273, h9095, h9161, h9171, hlam]
                  · linarith only [h5743, h9096, h9165, h9166, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9202 | h9202
                  · linarith only [h5743, h9098, h9165, h9202, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9204 | h9204
                    · linarith only [h5743, h9165, h9204, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9206 | h9206
                      · linarith only [h8272, h8273, h9163, h9202, h9206, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9208 | h9208
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9209 | h9209
                          · rcases h0bigk with h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c | h9210c
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [hlam, p9210_0]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h0, hlam, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h5743, hlam, p9210_0]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h6852, hlam, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h7594, hlam, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h8273, h9163, hc01, hc12, hlam, hphi, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [hlam, p9210_0]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h5743, h8273, h9163, hc01, hc12, hlam, hphi, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h8273, hlam, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h8273, h9163, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h5743, hc01, hc13, hlam, hphi, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h8272, hlam, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [hlam, p9210_0]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h9096, hlam, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h9098, hlam, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h8273, h9163, hc01, hc12, hlam, hphi, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h8273, h9163, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h8273, h9163, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [hlam, p9210_0]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h5743, h8273, h9098, h9163, hc01, hc12, hlam, hphi, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h9095, hlam, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h0, h5743, h9095, hc01, hc12, hlam, hphi, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [h9161, hlam, p9210_1]
                            · have p9210_0 := h9210c.1
                              have p9210_1 := h9210c.2.1
                              have p9210_2 := h9210c.2.2.1
                              have p9210_3 := h9210c.2.2.2
                              linarith only [hlam, p9210_0]
                          · linarith only [h5743, h9165, h9209, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h8273, h9095, h9161, h9208, hlam]
              · linarith only [h8273, h9095, h9163, h9164, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9239 | h9239
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9240 | h9240
                · linarith only [h5743, h9096, h9162, h9163, h9240, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9242 | h9242
                  · linarith only [h5743, h9098, h9162, h9163, h9242, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9244 | h9244
                    · linarith only [h0, h6852, h8272, h9163, h9240, h9244, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9246 | h9246
                      · linarith only [h0, h5743, h8272, h9163, h9242, h9244, h9246, hc03, hc34, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9248 | h9248
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9249 | h9249
                          · rcases h0bigk with h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c | h9250c
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [hlam, p9250_0]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h0, hlam, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h5743, hlam, p9250_0]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h6852, hlam, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h7594, hlam, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h0, h9163, h9244, hc01, hc34, hlam, hphi, ht12, ht23, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [hlam, p9250_0]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h0, h9163, h9244, hc03, hc34, hlam, hphi, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h8273, hlam, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h0, h9163, h9244, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h5743, hc01, hc13, hlam, hphi, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h8272, hlam, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [hlam, p9250_0]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h9096, hlam, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h9098, hlam, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h6852, hc01, hc14, hlam, hphi, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h8273, h9244, hc02, hc34, hlam, hphi, ht23, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h8273, h9244, hc03, hc34, hlam, hphi, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [hlam, p9250_0]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h5743, h8273, h9098, h9244, hc01, hc34, hlam, hphi, ht12, ht23, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h7594, h9163, h9239, h9244, hc01, hc34, hlam, hphi, ht12, ht23, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h9095, hlam, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h5743, h7594, h9163, h9239, h9244, hc01, hc34, hlam, hphi, ht12, ht23, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [h9161, hlam, p9250_1]
                            · have p9250_0 := h9250c.1
                              have p9250_1 := h9250c.2.1
                              have p9250_2 := h9250c.2.2.1
                              have p9250_3 := h9250c.2.2.2
                              linarith only [hlam, p9250_0]
                          · linarith only [h0, h9163, h9244, h9249, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h5743, h9161, h9163, h9239, h9242, h9248, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h9095, h9239, hlam]
          · linarith only [h0, h8272, h9162, hlam]
        · linarith only [h8273, h9095, h9161, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9281 | h9281
    · linarith only [h8272, h8273, h9281, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9283 | h9283
      · linarith only [h8272, h9095, h9283, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9285 | h9285
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9286 | h9286
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9287 | h9287
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9288 | h9288
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9289 | h9289
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9290 | h9290
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9291 | h9291
                    · linarith only [h8272, h9095, h9281, h9291, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9293 | h9293
                      · linarith only [h5743, h8272, h8273, h9283, h9286, h9289, h9291, h9293, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9295 | h9295
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9296 | h9296
                          · rcases h0bigk with h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c | h9297c
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [hlam, p9297_0]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h0, hlam, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h5743, hlam, p9297_0]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h6852, hlam, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h7594, hlam, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h9095, h9286, h9289, h9291, h9295, hc01, hc12, hlam, hphi, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [hlam, p9297_0]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h5743, h9095, h9286, h9289, h9291, h9295, hc01, hc12, hlam, hphi, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h8273, hlam, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h9095, hlam, p9297_0]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h5743, h9286, hc01, hc12, hlam, hphi, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h8272, hlam, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [hlam, p9297_0]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h9281, hlam, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h9283, hlam, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h6852, hc01, hc14, hlam, hphi, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h8273, h9286, h9289, h9291, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h8273, h9286, h9289, h9291, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [hlam, p9297_0]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h8272, h8273, h9095, h9286, h9289, h9291, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h8272, h9095, h9286, h9289, h9291, h9295, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h5743, h9095, h9286, h9289, h9291, h9295, hc01, hc12, hlam, hphi, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [h9285, hlam, p9297_1]
                            · have p9297_0 := h9297c.1
                              have p9297_1 := h9297c.2.1
                              have p9297_2 := h9297c.2.2.1
                              have p9297_3 := h9297c.2.2.2
                              linarith only [hlam, p9297_0]
                          · linarith only [h8273, h9285, h9291, h9296, hlam]
                        · linarith only [h8273, h9285, h9295, hlam]
                  · linarith only [h5743, h9281, h9289, h9290, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9326 | h9326
                  · linarith only [h5743, h9283, h9289, h9326, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9328 | h9328
                    · linarith only [h8272, h9095, h9288, h9289, h9328, hc13, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9330 | h9330
                      · linarith only [h8272, h8273, h9287, h9326, h9330, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9332 | h9332
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9333 | h9333
                          · rcases h0bigk with h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [hlam, p9334_0]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h0, hlam, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h5743, hlam, p9334_0]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h6852, hlam, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h7594, hlam, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h9095, h9288, hc01, hc15, hlam, hphi, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [hlam, p9334_0]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h5743, h9095, h9288, hc01, hc15, hlam, hphi, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h8273, hlam, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h9095, hlam, p9334_0]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h5743, hc01, hc13, hlam, hphi, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h8272, hlam, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [hlam, p9334_0]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h9281, hlam, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h9283, hlam, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h8273, h9287, hc01, hc12, hlam, hphi, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h8273, h9287, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h5743, h8273, h9287, hc01, hc12, hlam, hphi, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [hlam, p9334_0]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h8273, h9287, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h8272, h9095, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h5743, h9283, hc01, hc35, hlam, hphi, ht12, ht23, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [h9285, hlam, p9334_1]
                            · have p9334_0 := h9334c.1
                              have p9334_1 := h9334c.2.1
                              have p9334_2 := h9334c.2.2.1
                              have p9334_3 := h9334c.2.2.2
                              linarith only [hlam, p9334_0]
                          · linarith only [h8273, h9285, h9287, h9289, h9333, hlam]
                        · linarith only [h8273, h9285, h9332, hlam]
              · linarith only [h8272, h8273, h9287, h9288, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9363 | h9363
              · linarith only [h8272, h9095, h9287, h9363, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9365 | h9365
                · linarith only [h5743, h9281, h9286, h9287, h9365, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9367 | h9367
                  · linarith only [h9283, h9365, h9367, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9369 | h9369
                    · linarith only [h0, h8272, h9287, h9365, h9369, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9371 | h9371
                      · linarith only [h0, h7594, h8272, h9367, h9371, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9373 | h9373
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9374 | h9374
                          · rcases h0bigk with h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c | h9375c
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [hlam, p9375_0]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h0, hlam, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h5743, hlam, p9375_0]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h6852, hlam, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h7594, hlam, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h7594, h9095, hc01, hc15, hlam, hphi, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [hlam, p9375_0]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h0, h5743, hc01, hc12, hlam, hphi, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h8273, hlam, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h9095, hlam, p9375_0]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h5743, hc01, hc13, hlam, hphi, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h8272, hlam, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [hlam, p9375_0]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h9281, hlam, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h9283, hlam, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h6852, h9287, h9369, hc01, hc34, hlam, hphi, ht12, ht23, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h6852, h9287, h9369, hc02, hc34, hlam, hphi, ht23, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h6852, h9287, h9369, hc03, hc34, hlam, hphi, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [hlam, p9375_0]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h6852, h7594, h9287, h9369, hc01, hc34, hlam, hphi, ht12, ht23, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h8272, h9095, h9371, hc23, hc35, hlam, hphi, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h5743, h9095, h9371, hc01, hc35, hlam, hphi, ht12, ht23, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [h9285, hlam, p9375_1]
                            · have p9375_0 := h9375c.1
                              have p9375_1 := h9375c.2.1
                              have p9375_2 := h9375c.2.2.1
                              have p9375_3 := h9375c.2.2.2
                              linarith only [hlam, p9375_0]
                          · linarith only [h6852, h9285, h9287, h9369, h9374, hlam]
                        · linarith only [h6852, h9285, h9287, h9373, hlam]
          · linarith only [h0, h8272, h9286, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9404 | h9404
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9405 | h9405
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9406 | h9406
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9407 | h9407
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9408 | h9408
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9409 | h9409
                    · linarith only [h5743, h8272, h8273, h9281, h9283, h9285, h9408, h9409, hc01, hc13, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9411 | h9411
                      · linarith only [h8272, h8273, h9283, h9404, h9407, h9409, h9411, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9413 | h9413
                        · linarith only [h6852, h9285, h9404, h9407, h9409, h9413, hc01, hc12, hlam, hphi]
                        · linarith only [h8272, h8273, h9413, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h5743, h9281, h9407, h9408, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9417 | h9417
                  · linarith only [h5743, h9283, h9407, h9417, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9419 | h9419
                    · linarith only [h8272, h8273, h9405, h9407, h9419, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9421 | h9421
                      · linarith only [h8272, h8273, h9405, h9417, h9421, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9423 | h9423
                        · linarith only [h8272, h8273, h9285, h9405, h9423, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h8272, h8273, h9423, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h8272, h8273, h9405, h9406, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9427 | h9427
              · linarith only [h8272, h9095, h9405, h9427, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9429 | h9429
                · linarith only [h5743, h9281, h9404, h9405, h9429, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9431 | h9431
                  · linarith only [h5743, h9283, h9429, h9431, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9433 | h9433
                    · linarith only [h0, h8272, h9405, h9429, h9433, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9435 | h9435
                      · linarith only [h5743, h9431, h9435, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9437 | h9437
                        · linarith only [h8272, h8273, h9285, h9433, h9437, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h9405, h9437, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h7594, h8272, h8273, h9285, h9404, hc01, hc15, hlam, hphi]

set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 2 4 (by decide) (by decide) with h8273 | h8273
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h8273
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg5743 hg6852 h7594 h8272 h8273

set_option maxHeartbeats 5896000 in
set_option maxHeartbeats 5896000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s9_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6852 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h7594 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8272 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h9441 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0bigk := hb0.1
  have h0 := hg0
  have h5743 := hg5743
  have h6852 := hg6852
  rcases m.htr 0 2 5 (by decide) (by decide) with h9442 | h9442
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9443 | h9443
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9444 | h9444
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9445 | h9445
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9446 | h9446
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9447 | h9447
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9448 | h9448
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9449 | h9449
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9450 | h9450
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9451 | h9451
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9452 | h9452
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9453 | h9453
                        · linarith only [h8272, h9441, h9446, h9453, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h8272, h9441, h9445, h9446, h9453, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h8272, h9444, h9452, hlam]
                    · linarith only [h8272, h9443, h9451, hlam]
                  · linarith only [h8272, h9441, h9444, h9445, h9446, h9450, hlam]
                · linarith only [h8272, h9441, h9443, h9446, h9449, hlam]
              · linarith only [h8272, h9442, h9446, h9448, hlam]
            · linarith only [h8272, h9446, h9447, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9462 | h9462
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9463 | h9463
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9464 | h9464
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9465 | h9465
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9466 | h9466
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9467 | h9467
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9468 | h9468
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9469 | h9469
                          · rcases h0bigk with h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c | h9470c
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [hlam, p9470_0]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h0, hlam, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h5743, hlam, p9470_0]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h6852, hlam, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h7594, hlam, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h0, h9446, hc01, hc23, hlam, hphi, ht12, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [hlam, p9470_0]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h8272, hlam, p9470_0]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h0, h9446, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h0, h7594, h9446, hc01, hc23, hlam, hphi, ht12, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h5743, h9446, hc01, hc23, hlam, hphi, ht12, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h5743, h9446, hc02, hc23, hlam, hphi, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [hlam, p9470_0]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h5743, h9441, h9446, h9466, h9469, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h5743, h7594, h9446, hc01, hc23, hlam, hphi, ht12, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h6852, hc01, hc14, hlam, hphi, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h9441, hlam, p9470_0]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h9443, hlam, p9470_0]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [hlam, p9470_0]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h0, h7594, h9441, h9446, hc01, hc23, hlam, hphi, ht12, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h9442, hlam, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h9444, hlam, p9470_0]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [h9445, hlam, p9470_1]
                            · have p9470_0 := h9470c.1
                              have p9470_1 := h9470c.2.1
                              have p9470_2 := h9470c.2.2.1
                              have p9470_3 := h9470c.2.2.2
                              linarith only [hlam, p9470_0]
                          · linarith only [h0, h9441, h9446, h9468, h9469, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9497 | h9497
                          · linarith only [h9466, h9468, h9497, hlam]
                          · rcases h0bigk with h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c | h9499c
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [hlam, p9499_0]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h0, hlam, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h5743, hlam, p9499_0]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h6852, hlam, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h7594, hlam, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h0, h9446, hc01, hc23, hlam, hphi, ht12, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [hlam, p9499_0]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h8272, hlam, p9499_0]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h0, h9446, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h0, h9446, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h5743, h9446, hc01, hc23, hlam, hphi, ht12, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h5743, h9446, hc02, hc23, hlam, hphi, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [hlam, p9499_0]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h5743, h9445, h9446, h9466, h9468, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h5743, h7594, h9446, hc01, hc23, hlam, hphi, ht12, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h0, h9441, h9446, hc01, hc23, hlam, hphi, ht12, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h9441, hlam, p9499_0]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h9443, hlam, p9499_0]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [hlam, p9499_0]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h0, h7594, h9441, h9446, hc01, hc23, hlam, hphi, ht12, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h7594, h9446, h9463, hc01, hc23, hlam, hphi, ht12, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h9442, hlam, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h9444, hlam, p9499_0]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [h9445, hlam, p9499_1]
                            · have p9499_0 := h9499c.1
                              have p9499_1 := h9499c.2.1
                              have p9499_2 := h9499c.2.2.1
                              have p9499_3 := h9499c.2.2.2
                              linarith only [hlam, p9499_0]
                      · linarith only [h0, h9446, h9467, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h9446, h9466, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h5743, h9441, h9444, h9445, h9446, h9465, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h5743, h9443, h9464, hlam]
              · linarith only [h0, h9442, h9463, hlam]
            · linarith only [h0, h9441, h9462, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9531 | h9531
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9532 | h9532
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9533 | h9533
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9534 | h9534
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9535 | h9535
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9536 | h9536
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9537 | h9537
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9538 | h9538
                        · linarith only [h5743, h6852, h8272, h9441, h9445, h9538, hc01, hc13, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9540 | h9540
                          · linarith only [h6852, h8272, h9442, h9445, h9531, h9536, h9538, h9540, hc01, hc12, hlam, hphi]
                          · rcases h0bigk with h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c | h9542c
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h0, hlam, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h5743, hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h6852, hlam, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h7594, hlam, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h8272, h9531, hc01, hc12, hlam, hphi, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h8272, hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h6852, h8272, h9531, hc01, hc12, hlam, hphi, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h8272, h9531, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h8272, h9531, hc01, hc12, hlam, hphi, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h8272, h9531, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h6852, h8272, h9531, hc01, hc12, hlam, hphi, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h7594, h8272, h9531, hc01, hc12, hlam, hphi, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h9445, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h9441, hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h9443, hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h9445, hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h9442, hlam, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h9444, hlam, p9542_0]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [h8272, h9442, h9531, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9542_1]
                            · have p9542_0 := h9542c.1
                              have p9542_1 := h9542c.2.1
                              have p9542_2 := h9542c.2.2.1
                              have p9542_3 := h9542c.2.2.2
                              linarith only [hlam, p9542_0]
                      · linarith only [h8272, h9444, h9537, hlam]
                    · linarith only [h8272, h9443, h9536, hlam]
                  · linarith only [h5743, h8272, h9442, h9444, h9535, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h5743, h8272, h9441, h9443, h9534, hlam]
              · linarith only [h8272, h9442, h9533, hc12, hc23, hlam, hphi]
            · linarith only [h8272, h9441, h9531, h9532, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9574 | h9574
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9575 | h9575
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9576 | h9576
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9577 | h9577
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9578 | h9578
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9579 | h9579
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9580 | h9580
                        · linarith only [h9441, h9445, h9580, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9582 | h9582
                          · linarith only [h5743, h6852, h9443, h9445, h9531, h9582, hc01, hc23, hlam, hphi, ht12]
                          · rcases h0bigk with h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c | h9584c
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h0, hlam, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h5743, hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h6852, hlam, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h7594, hlam, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h0, h9531, hc01, hc23, hlam, hphi, ht12, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h8272, hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h0, h6852, h9531, hc01, hc23, hlam, hphi, ht12, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h0, h6852, h9445, h9531, hc01, hc23, hlam, hphi, ht12, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h5743, h9531, hc01, hc23, hlam, hphi, ht12, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h5743, h9531, hc02, hc23, hlam, hphi, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h5743, h6852, h9531, hc01, hc23, hlam, hphi, ht12, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h5743, h6852, h9445, h9531, hc01, hc23, hlam, hphi, ht12, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h9445, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h9441, hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h9443, hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h9445, hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h7594, h9531, h9575, hc01, hc23, hlam, hphi, ht12, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h9442, hlam, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h9444, hlam, p9584_0]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [h7594, h9531, h9575, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9584_1]
                            · have p9584_0 := h9584c.1
                              have p9584_1 := h9584c.2.1
                              have p9584_2 := h9584c.2.2.1
                              have p9584_3 := h9584c.2.2.2
                              linarith only [hlam, p9584_0]
                      · linarith only [h0, h9531, h9579, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h9531, h9578, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h5743, h7594, h9444, h9531, h9575, h9577, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h5743, h9443, h9576, hlam]
              · linarith only [h0, h9442, h9575, hlam]
            · linarith only [h0, h9441, h9574, hlam]
      · linarith only [h8272, h9442, h9444, hlam]
    · linarith only [h8272, h9441, h9443, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h9618 | h9618
    · rcases m.htr 0 3 5 (by decide) (by decide) with h9619 | h9619
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9620 | h9620
        · linarith only [h9441, h9442, h9620, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9622 | h9622
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9623 | h9623
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9624 | h9624
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9625 | h9625
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9626 | h9626
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9627 | h9627
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9628 | h9628
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9629 | h9629
                        · linarith only [h9441, h9442, h9620, h9624, h9629, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9631 | h9631
                          · linarith only [h9441, h9442, h9627, h9629, h9631, hlam]
                          · rcases h0bigk with h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c | h9633c
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h0, hlam, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h5743, hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h6852, hlam, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h7594, hlam, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h9442, h9622, h9628, hc01, hc12, hlam, hphi, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h8272, hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h6852, h9442, h9622, h9628, hc01, hc12, hlam, hphi, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h9442, hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h5743, hc01, hc13, hlam, hphi, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h8272, h9622, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h6852, h8272, h9622, hc01, hc12, hlam, hphi, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h8272, h9441, h9442, h9622, h9627, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h6852, hc01, hc14, hlam, hphi, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h9441, hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h9618, hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h9620, hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h9441, h9442, h9622, h9627, h9628, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h9619, hlam, p9633_0]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [h9442, h9622, h9628, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p9633_1]
                            · have p9633_0 := h9633c.1
                              have p9633_1 := h9633c.2.1
                              have p9633_2 := h9633c.2.2.1
                              have p9633_3 := h9633c.2.2.2
                              linarith only [hlam, p9633_0]
                      · linarith only [h8272, h9619, h9628, hlam]
                    · linarith only [h8272, h9618, h9627, hlam]
                  · linarith only [h5743, h8272, h9619, h9626, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h8272, h9618, h9622, h9625, hlam]
              · linarith only [h8272, h9441, h9622, h9624, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h8272, h9441, h9622, h9623, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9665 | h9665
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9666 | h9666
              · linarith only [h9441, h9442, h9622, h9666, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9668 | h9668
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9669 | h9669
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9670 | h9670
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9671 | h9671
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9672 | h9672
                        · linarith only [h0, h7594, h9441, h9620, h9666, h9671, h9672, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9674 | h9674
                          · linarith only [h0, h9666, h9672, h9674, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h0bigk with h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c | h9676c
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h0, hlam, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h5743, hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h6852, hlam, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h7594, hlam, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h8272, hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h0, h9666, h9672, hc04, hc45, hlam, hphi, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h9442, hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h5743, h9622, hc01, hc23, hlam, hphi, ht12, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h5743, h9622, hc02, hc23, hlam, hphi, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h5743, h6852, h9622, hc01, hc23, hlam, hphi, ht12, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h5743, h9441, h9442, h9622, h9670, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h6852, hc01, hc14, hlam, hphi, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h9441, hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h9618, hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h9620, hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h9441, h9442, h9670, h9672, hc34, hc45, hlam, hphi, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h9619, hlam, p9676_0]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [h9442, h9672, hc04, hc45, hlam, hphi, p9676_1]
                            · have p9676_0 := h9676c.1
                              have p9676_1 := h9676c.2.1
                              have p9676_2 := h9676c.2.2.1
                              have p9676_3 := h9676c.2.2.2
                              linarith only [hlam, p9676_0]
                      · linarith only [h5743, h9619, h9622, h9671, hlam]
                    · linarith only [h5743, h9618, h9622, h9670, hlam]
                  · linarith only [h5743, h9619, h9669, hlam]
                · linarith only [h6852, h9618, h9622, h9665, h9668, hlam]
            · linarith only [h0, h9441, h9665, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h9707 | h9707
        · linarith only [h9441, h9442, h9707, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h9709 | h9709
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9710 | h9710
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9711 | h9711
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9712 | h9712
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9713 | h9713
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9714 | h9714
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9715 | h9715
                      · linarith only [h8272, h9441, h9619, h9709, h9714, h9715, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h8272, h9441, h9713, h9714, h9715, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8272, h9618, h9714, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9719 | h9719
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9720 | h9720
                      · linarith only [h5743, h9713, h9720, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9722 | h9722
                        · linarith only [h8272, h9441, h9709, h9713, h9722, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9724 | h9724
                          · linarith only [h8272, h9441, h9442, h9709, h9713, h9719, h9722, h9724, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h8272, h9441, h9709, h9713, h9719, h9724, hc34, hc45, hlam, hphi]
                    · linarith only [h8272, h9441, h9618, h9719, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h8272, h9441, h9618, h9709, h9712, hlam]
              · linarith only [h8272, h9441, h9709, h9711, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h8272, h9441, h9709, h9710, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h9731 | h9731
            · rcases m.htr 1 2 5 (by decide) (by decide) with h9732 | h9732
              · linarith only [h9441, h9442, h9709, h9732, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h9734 | h9734
                · rcases m.htr 1 3 5 (by decide) (by decide) with h9735 | h9735
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9736 | h9736
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9737 | h9737
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9738 | h9738
                        · linarith only [h8272, h9441, h9619, h9709, h9735, h9738, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9740 | h9740
                          · linarith only [h8272, h9441, h9619, h9709, h9732, h9735, h9736, h9738, h9740, hc12, hc23, hlam, hphi]
                          · rcases h0bigk with h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c | h9742c
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h0, hlam, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h5743, hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h6852, hlam, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h7594, hlam, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h8272, h9619, h9709, h9735, hc01, hc23, hlam, hphi, ht12, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h8272, hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h8272, h9619, h9709, h9735, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h9442, hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h9619, h9709, h9735, hc01, hc23, hlam, hphi, ht12, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h9619, h9709, h9735, hc02, hc23, hlam, hphi, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h6852, h9619, h9709, h9735, hc01, hc23, hlam, hphi, ht12, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h9619, hlam, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h6852, h9731, hc01, hc12, hlam, hphi, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h9441, hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h9618, hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h9707, hlam, p9742_0]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h7594, hc01, hc15, hlam, hphi, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h9441, h9442, h9736, h9738, hc34, hc45, hlam, hphi, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h8272, h9441, h9619, h9709, h9735, h9736, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [h9619, h9709, h9735, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p9742_1]
                            · have p9742_0 := h9742c.1
                              have p9742_1 := h9742c.2.1
                              have p9742_2 := h9742c.2.2.1
                              have p9742_3 := h9742c.2.2.2
                              linarith only [hlam, p9742_0]
                      · linarith only [h9709, h9735, h9737, hlam]
                    · linarith only [h5743, h9618, h9709, h9736, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9770 | h9770
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9771 | h9771
                      · linarith only [h0, h9709, h9735, h9771, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h6852, h9709, h9731, h9771, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h6852, h9709, h9731, h9770, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h5743, h8272, h9441, h9618, h9734, hlam]
            · linarith only [h0, h5743, h8272, h9441, h9731, hc01, hc13, hlam, hphi]
    · linarith only [h8272, h9441, h9618, hlam]

end R2N4
