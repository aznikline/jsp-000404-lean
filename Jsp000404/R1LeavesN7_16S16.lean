import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8198000 in
set_option maxHeartbeats 8198000 in
theorem r1l7_21_15_H_I_L_I_s8 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1bigk := hb1.1
  have h0 := hg0
  have h6137 := hg6137
  rcases m.htr 0 1 4 (by decide) (by decide) with h7252 | h7252
  · rcases m.htr 0 1 5 (by decide) (by decide) with h7253 | h7253
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7254 | h7254
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7255 | h7255
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7256 | h7256
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7257 | h7257
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7258 | h7258
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7259 | h7259
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7260 | h7260
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7261 | h7261
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7262 | h7262
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7263 | h7263
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7264 | h7264
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7265 | h7265
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7266 | h7266
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7267 | h7267
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7268 | h7268
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7269 | h7269
                                    · rcases h1bigk with h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c | h7270c
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h0, hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h6137, hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7261, h7266, h7269, hc01, hc45, hlam, hphi, ht0b, ht5b, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h6137, hc13, hc15, hlam, hphi, ht01, ht0b, ht5b, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h6137, h7252, h7261, h7266, h7269, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7261, h7266, h7269, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        rcases p7270_3 (m.d 0 1) (by simp) with h7280 | h7280
                                        · linarith only [h0, h7280, hlam]
                                        · linarith only [h7253, h7280, hlam]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7252, h7261, h7266, h7269, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7260, hlam, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7260, h7261, h7266, h7269, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        rcases p7270_3 (m.d 0 1) (by simp) with h7287 | h7287
                                        · linarith only [h6137, h7287, hlam]
                                        · linarith only [h7253, h7287, hlam]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7252, hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7261, hlam, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7263, hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7252, h7262, h7267, h7269, hc01, hc45, hlam, hphi, ht0b, ht5b, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7253, hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7262, hlam, p7270_1]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7264, hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [h7265, hlam, p7270_0]
                                      · have p7270_0 := h7270c.1
                                        have p7270_1 := h7270c.2.1
                                        have p7270_2 := h7270c.2.2.1
                                        have p7270_3 := h7270c.2.2.2
                                        linarith only [hlam, p7270_0]
                                    · linarith only [h6137, h7252, h7260, h7265, h7269, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h6137, h7252, h7260, h7265, h7266, h7268, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h6137, h7252, h7260, h7264, h7265, h7266, h7267, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7303 | h7303
                                · linarith only [h6137, h7252, h7260, h7263, h7266, h7303, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7305 | h7305
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7306 | h7306
                                    · rcases h1bigk with h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c | h7307c
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h0, hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h6137, hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h6137, h7260, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h6137, h7260, h7264, h7303, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h6137, hc01, hc12, hlam, hphi, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7264, h7265, h7303, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7264, h7303, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7252, h7264, h7265, h7303, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7260, hlam, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7260, h7264, h7265, h7303, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7260, h7264, h7303, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7252, hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7261, hlam, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7263, hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7252, h7264, h7303, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7253, hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7262, hlam, p7307_1]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7264, hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [h7265, hlam, p7307_0]
                                      · have p7307_0 := h7307c.1
                                        have p7307_1 := h7307c.2.1
                                        have p7307_2 := h7307c.2.2.1
                                        have p7307_3 := h7307c.2.2.2
                                        linarith only [hlam, p7307_0]
                                    · linarith only [h6137, h7252, h7260, h7261, h7305, h7306, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h6137, h7252, h7260, h7265, h7305, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7335 | h7335
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7336 | h7336
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7337 | h7337
                                  · linarith only [h7261, h7265, h7337, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7339 | h7339
                                    · linarith only [h7263, h7265, h7339, hlam]
                                    · rcases h1bigk with h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c | h7341c
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h0, hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h6137, hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h6137, h7260, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h6137, h7260, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h6137, hc01, hc12, hlam, hphi, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        rcases p7341_3 (m.d 0 1) (by simp) with h7350 | h7350
                                        · linarith only [h0, h7350, hlam]
                                        · linarith only [h7252, h7350, hlam]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        rcases p7341_3 (m.d 0 1) (by simp) with h7353 | h7353
                                        · linarith only [h0, h7353, hlam]
                                        · linarith only [h7253, h7353, hlam]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7252, h7259, h7261, h7265, h7335, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7260, hlam, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        rcases p7341_3 (m.d 0 1) (by simp) with h7359 | h7359
                                        · linarith only [h6137, h7359, hlam]
                                        · linarith only [h7252, h7359, hlam]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        rcases p7341_3 (m.d 0 1) (by simp) with h7362 | h7362
                                        · linarith only [h6137, h7362, hlam]
                                        · linarith only [h7253, h7362, hlam]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7252, hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7261, hlam, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7263, hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7265, hlam, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7253, hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7262, hlam, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7264, hlam, p7341_0]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [h7253, h7261, h7335, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7341_1]
                                      · have p7341_0 := h7341c.1
                                        have p7341_1 := h7341c.2.1
                                        have p7341_2 := h7341c.2.2.1
                                        have p7341_3 := h7341c.2.2.2
                                        linarith only [hlam, p7341_0]
                                · linarith only [h6137, h7252, h7259, h7260, h7264, h7265, h7335, h7336, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h6137, h7252, h7259, h7260, h7263, h7265, h7335, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h0, h6137, h7254, h7258, h7264, hc01, hc12, hlam, hphi]
                        · linarith only [h6137, h7252, h7254, h7257, h7263, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h7256, h7262, hlam]
                    · linarith only [h0, h7255, h7261, hlam]
                  · linarith only [h0, h7254, h7260, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7382 | h7382
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7383 | h7383
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7384 | h7384
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7385 | h7385
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7386 | h7386
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7387 | h7387
                            · linarith only [h0, h7252, h7259, h7387, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7389 | h7389
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7390 | h7390
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7391 | h7391
                                  · linarith only [h7252, h7259, h7383, h7391, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7393 | h7393
                                    · linarith only [h7252, h7259, h7383, h7389, h7393, hlam]
                                    · rcases h1bigk with h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c | h7395c
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h0, hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h6137, hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h6137, h7382, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h6137, h7382, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h6137, hc01, hc12, hlam, hphi, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        rcases p7395_3 (m.d 0 1) (by simp) with h7404 | h7404
                                        · linarith only [h0, h7404, hlam]
                                        · linarith only [h7252, h7404, hlam]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        rcases p7395_3 (m.d 0 1) (by simp) with h7407 | h7407
                                        · linarith only [h0, h7407, hlam]
                                        · linarith only [h7253, h7407, hlam]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7253, h7383, h7387, h7389, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7382, hlam, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        rcases p7395_3 (m.d 0 1) (by simp) with h7413 | h7413
                                        · linarith only [h6137, h7413, hlam]
                                        · linarith only [h7252, h7413, hlam]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        rcases p7395_3 (m.d 0 1) (by simp) with h7416 | h7416
                                        · linarith only [h6137, h7416, hlam]
                                        · linarith only [h7253, h7416, hlam]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7252, hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7383, hlam, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7385, hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7387, hlam, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7253, hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7384, hlam, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7386, hlam, p7395_0]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [h7253, h7383, h7389, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7395_1]
                                      · have p7395_0 := h7395c.1
                                        have p7395_1 := h7395c.2.1
                                        have p7395_2 := h7395c.2.2.1
                                        have p7395_3 := h7395c.2.2.2
                                        linarith only [hlam, p7395_0]
                                · linarith only [h6137, h7253, h7382, h7386, h7389, h7390, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7430 | h7430
                                · linarith only [h6137, h7252, h7382, h7385, h7389, h7430, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7432 | h7432
                                  · linarith only [h6137, h7253, h7259, h7382, h7385, h7387, h7389, h7432, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7434 | h7434
                                    · linarith only [h7252, h7259, h7385, h7434, hlam]
                                    · rcases h1bigk with h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c | h7436c
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h0, hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h6137, hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h6137, h7382, h7385, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h6137, h7382, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h6137, hc01, hc12, hlam, hphi, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7385, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7385, h7387, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7252, h7385, h7389, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7382, hlam, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7382, h7385, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7382, h7385, h7387, h7389, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7252, hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7383, hlam, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7385, hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7387, hlam, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7253, hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7384, hlam, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7386, hlam, p7436_0]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [h7385, h7389, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7436_1]
                                      · have p7436_0 := h7436c.1
                                        have p7436_1 := h7436c.2.1
                                        have p7436_2 := h7436c.2.2.1
                                        have p7436_3 := h7436c.2.2.2
                                        linarith only [hlam, p7436_0]
                          · linarith only [h6137, h7253, h7258, h7386, hlam]
                        · linarith only [h6137, h7257, h7385, hlam]
                      · linarith only [h0, h7256, h7384, hlam]
                    · linarith only [h0, h7255, h7383, hlam]
                  · linarith only [h0, h7254, h7382, hlam]
              · linarith only [h6137, h7253, h7258, hlam]
            · linarith only [h6137, h7252, h7257, hlam]
          · linarith only [h0, h7253, h7256, hlam]
        · linarith only [h6137, h7252, h7254, h7255, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7471 | h7471
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7472 | h7472
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7473 | h7473
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7474 | h7474
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7475 | h7475
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7476 | h7476
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7477 | h7477
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7478 | h7478
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7479 | h7479
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7480 | h7480
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7481 | h7481
                            · linarith only [h0, h7252, h7254, h7476, h7481, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h7252, h7254, h7475, h7476, h7481, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h6137, h7253, h7474, h7480, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h7254, h7473, h7476, h7479, hlam]
                      · linarith only [h7254, h7472, h7478, hc12, hc23, hlam, hphi]
                    · linarith only [h0, h7254, h7476, h7477, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7488 | h7488
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7489 | h7489
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7490 | h7490
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7491 | h7491
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7492 | h7492
                            · linarith only [h0, h7252, h7476, h7492, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · linarith only [h0, h7252, h7475, h7476, h7492, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h6137, h7474, h7491, hlam]
                        · linarith only [h6137, h7473, h7490, hlam]
                      · linarith only [h0, h7472, h7489, hlam]
                    · linarith only [h0, h7471, h7488, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7499 | h7499
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7500 | h7500
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7501 | h7501
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7502 | h7502
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7503 | h7503
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7504 | h7504
                            · linarith only [h0, h7252, h7254, h7475, h7499, h7504, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7506 | h7506
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7507 | h7507
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7508 | h7508
                                  · linarith only [h7252, h7475, h7500, h7508, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7510 | h7510
                                    · linarith only [h7252, h7475, h7500, h7506, h7510, hlam]
                                    · rcases h1bigk with h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c | h7512c
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h0, hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h6137, hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h0, h7254, h7499, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h0, h7254, h7499, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h6137, h7252, h7500, h7506, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        rcases p7512_3 (m.d 0 1) (by simp) with h7521 | h7521
                                        · linarith only [h0, h7521, hlam]
                                        · linarith only [h7252, h7521, hlam]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        rcases p7512_3 (m.d 0 1) (by simp) with h7524 | h7524
                                        · linarith only [h0, h7524, hlam]
                                        · linarith only [h7253, h7524, hlam]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7253, h7500, h7504, h7506, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7499, hlam, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        rcases p7512_3 (m.d 0 1) (by simp) with h7530 | h7530
                                        · linarith only [h6137, h7530, hlam]
                                        · linarith only [h7252, h7530, hlam]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        rcases p7512_3 (m.d 0 1) (by simp) with h7533 | h7533
                                        · linarith only [h6137, h7533, hlam]
                                        · linarith only [h7253, h7533, hlam]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7252, hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7500, hlam, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7502, hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7504, hlam, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7253, hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7501, hlam, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7503, hlam, p7512_0]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [h7253, h7500, h7506, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7512_1]
                                      · have p7512_0 := h7512c.1
                                        have p7512_1 := h7512c.2.1
                                        have p7512_2 := h7512c.2.2.1
                                        have p7512_3 := h7512c.2.2.2
                                        linarith only [hlam, p7512_0]
                                · linarith only [h7254, h7474, h7507, hlam]
                              · linarith only [h7254, h7473, h7506, hlam]
                          · linarith only [h6137, h7254, h7474, h7503, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h7254, h7473, h7499, h7502, hlam]
                      · linarith only [h0, h7252, h7472, h7500, h7501, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h7254, h7499, h7500, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7552 | h7552
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7553 | h7553
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7554 | h7554
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7555 | h7555
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7556 | h7556
                            · linarith only [h0, h7252, h7475, h7499, h7556, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7558 | h7558
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7559 | h7559
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7560 | h7560
                                  · linarith only [h7252, h7475, h7552, h7560, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7562 | h7562
                                    · linarith only [h7252, h7475, h7552, h7558, h7562, hlam]
                                    · rcases h1bigk with h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c | h7564c
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h0, hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h6137, hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h0, h7499, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h0, h7499, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7499, hc01, hc23, hlam, hphi, ht12, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7499, hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7499, h7552, h7558, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7499, h7553, h7559, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7252, h7499, h7552, h7558, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h0, h7499, hc02, hc23, hlam, hphi, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        rcases p7564_3 (m.d 0 1) (by simp) with h7578 | h7578
                                        · linarith only [h6137, h7578, hlam]
                                        · linarith only [h7252, h7578, hlam]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        rcases p7564_3 (m.d 0 1) (by simp) with h7581 | h7581
                                        · linarith only [h6137, h7581, hlam]
                                        · linarith only [h7253, h7581, hlam]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7252, hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7552, hlam, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7554, hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7556, hlam, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7253, hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7553, hlam, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7555, hlam, p7564_0]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [h7253, h7552, h7558, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7564_1]
                                      · have p7564_0 := h7564c.1
                                        have p7564_1 := h7564c.2.1
                                        have p7564_2 := h7564c.2.2.1
                                        have p7564_3 := h7564c.2.2.2
                                        linarith only [hlam, p7564_0]
                                · linarith only [h0, h7499, h7559, hc01, hc35, hlam, hphi, ht12, ht23]
                              · linarith only [h0, h7253, h7499, h7552, h7556, h7558, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · linarith only [h6137, h7474, h7555, hlam]
                        · linarith only [h6137, h7473, h7475, h7554, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h7472, h7553, hlam]
                    · linarith only [h0, h7471, h7552, hlam]
              · linarith only [h0, h7253, h7254, h7474, hlam]
            · linarith only [h0, h7252, h7254, h7473, hlam]
          · linarith only [h0, h7253, h7472, hlam]
        · linarith only [h0, h7252, h7471, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h7604 | h7604
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7605 | h7605
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7606 | h7606
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7607 | h7607
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7608 | h7608
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7609 | h7609
                · linarith only [h7252, h7253, h7609, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7611 | h7611
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7612 | h7612
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7613 | h7613
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7614 | h7614
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7615 | h7615
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7616 | h7616
                            · linarith only [h7252, h7253, h7609, h7611, h7615, h7616, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7618 | h7618
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7619 | h7619
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7620 | h7620
                                  · linarith only [h7252, h7253, h7612, h7616, h7620, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7622 | h7622
                                    · linarith only [h7253, h7604, h7616, h7618, h7622, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                                    · rcases h1bigk with h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c | h7624c
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h0, hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h6137, hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7253, h7612, h7618, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7253, hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h6137, h7252, h7612, h7618, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        rcases p7624_3 (m.d 0 1) (by simp) with h7633 | h7633
                                        · linarith only [h0, h7633, hlam]
                                        · linarith only [h7252, h7633, hlam]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7252, h7253, h7612, h7618, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7252, h7612, h7618, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7611, hlam, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        rcases p7624_3 (m.d 0 1) (by simp) with h7640 | h7640
                                        · linarith only [h6137, h7640, hlam]
                                        · linarith only [h7252, h7640, hlam]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7252, h7253, h7611, h7612, h7618, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7252, hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7612, hlam, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7614, hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7616, hlam, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7252, h7612, h7618, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7613, hlam, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7615, hlam, p7624_0]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [h7612, h7616, h7618, hc34, hc45, hlam, hphi, p7624_1]
                                      · have p7624_0 := h7624c.1
                                        have p7624_1 := h7624c.2.1
                                        have p7624_2 := h7624c.2.2.1
                                        have p7624_3 := h7624c.2.2.2
                                        linarith only [hlam, p7624_0]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7654 | h7654
                                  · linarith only [h7252, h7253, h7612, h7616, h7654, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7656 | h7656
                                    · linarith only [h0, h7253, h7604, h7608, h7616, h7618, h7619, h7656, hc01, hc12, hlam, hphi]
                                    · rcases h1bigk with h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c | h7658c
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h0, hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h6137, hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h0, h7612, h7618, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7253, hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h6137, hc01, hc12, hlam, hphi, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        rcases p7658_3 (m.d 0 1) (by simp) with h7667 | h7667
                                        · linarith only [h0, h7667, hlam]
                                        · linarith only [h7252, h7667, hlam]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7253, h7608, h7619, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7252, h7612, h7618, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7611, hlam, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        rcases p7658_3 (m.d 0 1) (by simp) with h7674 | h7674
                                        · linarith only [h6137, h7674, hlam]
                                        · linarith only [h7252, h7674, hlam]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7252, h7253, h7611, h7612, h7618, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7252, hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7612, hlam, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7614, hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7616, hlam, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7252, h7612, h7618, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7613, hlam, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7615, hlam, p7658_0]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [h7612, h7616, h7618, hc34, hc45, hlam, hphi, p7658_1]
                                      · have p7658_0 := h7658c.1
                                        have p7658_1 := h7658c.2.1
                                        have p7658_2 := h7658c.2.2.1
                                        have p7658_3 := h7658c.2.2.2
                                        linarith only [hlam, p7658_0]
                              · linarith only [h7252, h7253, h7614, h7616, h7618, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h0, h6137, h7604, h7608, h7615, hc01, hc12, hlam, hphi]
                        · linarith only [h6137, h7607, h7614, hlam]
                      · linarith only [h0, h7606, h7613, hlam]
                    · linarith only [h0, h7605, h7612, hlam]
                  · linarith only [h0, h7604, h7611, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7694 | h7694
                · linarith only [h6137, h7252, h7608, h7694, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7696 | h7696
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7697 | h7697
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7698 | h7698
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7699 | h7699
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7700 | h7700
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7701 | h7701
                            · linarith only [h6137, h7252, h7608, h7694, h7696, h7700, h7701, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7703 | h7703
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7704 | h7704
                                · linarith only [h6137, h7252, h7604, h7608, h7704, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7706 | h7706
                                  · linarith only [h6137, h7252, h7608, h7697, h7700, h7701, h7706, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7708 | h7708
                                    · linarith only [h6137, h7252, h7608, h7697, h7700, h7701, h7703, h7708, hlam]
                                    · rcases h1bigk with h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c | h7710c
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h0, hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h6137, hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h6137, h7608, h7697, h7700, h7703, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7253, hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7608, h7700, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        rcases p7710_3 (m.d 0 1) (by simp) with h7719 | h7719
                                        · linarith only [h0, h7719, hlam]
                                        · linarith only [h7252, h7719, hlam]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h6137, h7252, h7608, h7697, h7700, h7703, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7252, h7697, h7703, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7696, hlam, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        rcases p7710_3 (m.d 0 1) (by simp) with h7726 | h7726
                                        · linarith only [h6137, h7726, hlam]
                                        · linarith only [h7252, h7726, hlam]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h6137, h7252, h7608, h7696, h7697, h7700, h7703, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7252, hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7697, hlam, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7699, hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7701, hlam, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7252, h7697, h7703, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7698, hlam, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7700, hlam, p7710_0]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [h7697, h7701, h7703, hc34, hc45, hlam, hphi, p7710_1]
                                      · have p7710_0 := h7710c.1
                                        have p7710_1 := h7710c.2.1
                                        have p7710_2 := h7710c.2.2.1
                                        have p7710_3 := h7710c.2.2.2
                                        linarith only [hlam, p7710_0]
                              · linarith only [h7607, h7608, h7703, hc23, hc35, hlam, hphi]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7741 | h7741
                            · linarith only [h6137, h7252, h7700, h7741, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7743 | h7743
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7744 | h7744
                                · linarith only [h6137, h7700, h7744, hc01, hc23, hlam, hphi, ht12]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7746 | h7746
                                  · linarith only [h6137, h7252, h7697, h7700, h7741, h7746, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7748 | h7748
                                    · linarith only [h6137, h7252, h7697, h7700, h7741, h7743, h7748, hlam]
                                    · linarith only [h6137, h7252, h7697, h7700, h7743, h7748, hc34, hc45, hlam, hphi]
                              · linarith only [h6137, h7607, h7700, h7743, hc23, hc35, hlam, hphi]
                        · linarith only [h6137, h7252, h7607, h7699, hlam]
                      · linarith only [h0, h7606, h7698, hlam]
                    · linarith only [h0, h7605, h7697, hlam]
                  · linarith only [h0, h7604, h7696, hlam]
            · linarith only [h6137, h7252, h7607, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7757 | h7757
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7758 | h7758
              · linarith only [h7604, h7606, h7758, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7760 | h7760
                · linarith only [h0, h7252, h7606, h7760, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7762 | h7762
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7763 | h7763
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7764 | h7764
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7765 | h7765
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7766 | h7766
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7767 | h7767
                            · linarith only [h6137, h7252, h7604, h7606, h7760, h7764, h7767, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7769 | h7769
                              · linarith only [h7604, h7606, h7764, h7769, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7604, h7606, h7757, h7764, h7769, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7772 | h7772
                            · linarith only [h6137, h7252, h7604, h7606, h7764, h7772, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7774 | h7774
                              · linarith only [h7604, h7606, h7764, h7774, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h7604, h7606, h7757, h7764, h7774, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h6137, h7252, h7757, h7765, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7778 | h7778
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7779 | h7779
                          · linarith only [h6137, h7252, h7758, h7762, h7763, h7764, h7779, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7781 | h7781
                            · linarith only [h0, h7252, h7764, h7781, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7783 | h7783
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7784 | h7784
                                · linarith only [h0, h7604, h7764, h7779, h7784, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7786 | h7786
                                  · linarith only [h0, h7252, h7763, h7764, h7781, h7784, h7786, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · linarith only [h6137, h7252, h7762, h7763, h7764, h7783, h7786, hc34, hc45, hlam, hphi]
                              · linarith only [h7757, h7758, h7783, hc23, hc35, hlam, hphi]
                        · linarith only [h6137, h7252, h7757, h7778, hlam]
                    · linarith only [h6137, h7252, h7605, h7606, h7762, h7763, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h7604, h7762, hlam]
            · linarith only [h6137, h7252, h7757, hlam]
        · linarith only [h0, h7252, h7605, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h7795 | h7795
        · rcases m.htr 0 2 5 (by decide) (by decide) with h7796 | h7796
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7797 | h7797
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7798 | h7798
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7799 | h7799
                · linarith only [h7252, h7253, h7799, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7801 | h7801
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7802 | h7802
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7803 | h7803
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7804 | h7804
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7805 | h7805
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7806 | h7806
                            · linarith only [h7252, h7253, h7604, h7796, h7799, h7801, h7806, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7808 | h7808
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7809 | h7809
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7810 | h7810
                                  · linarith only [h7252, h7253, h7604, h7796, h7801, h7802, h7806, h7810, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7812 | h7812
                                    · linarith only [h7252, h7253, h7802, h7806, h7808, h7812, hlam]
                                    · rcases h1bigk with h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c | h7814c
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h0, hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h6137, hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7253, h7604, h7796, h7801, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7253, hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7604, h7801, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        rcases p7814_3 (m.d 0 1) (by simp) with h7823 | h7823
                                        · linarith only [h0, h7823, hlam]
                                        · linarith only [h7252, h7823, hlam]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7252, h7253, h7802, h7808, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7252, h7802, h7808, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7801, hlam, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        rcases p7814_3 (m.d 0 1) (by simp) with h7830 | h7830
                                        · linarith only [h6137, h7830, hlam]
                                        · linarith only [h7252, h7830, hlam]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7252, h7253, h7801, h7802, h7808, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7252, hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7802, hlam, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7804, hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7806, hlam, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7252, h7802, h7808, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7803, hlam, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7805, hlam, p7814_0]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [h7802, h7806, h7808, hc34, hc45, hlam, hphi, p7814_1]
                                      · have p7814_0 := h7814c.1
                                        have p7814_1 := h7814c.2.1
                                        have p7814_2 := h7814c.2.2.1
                                        have p7814_3 := h7814c.2.2.2
                                        linarith only [hlam, p7814_0]
                                · linarith only [h7252, h7253, h7604, h7796, h7798, h7802, h7808, h7809, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h7252, h7253, h7604, h7796, h7797, h7802, h7808, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h6137, h7252, h7604, h7796, h7798, h7801, h7802, h7805, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h7604, h7797, h7801, h7804, hlam]
                      · linarith only [h7604, h7796, h7803, hc12, hc23, hlam, hphi]
                    · linarith only [h7604, h7801, h7802, hc02, hc24, hlam, hphi]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7850 | h7850
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7851 | h7851
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7852 | h7852
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7853 | h7853
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7854 | h7854
                            · linarith only [h7252, h7253, h7801, h7851, h7854, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7856 | h7856
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7857 | h7857
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7858 | h7858
                                  · linarith only [h7252, h7253, h7850, h7854, h7858, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7860 | h7860
                                    · linarith only [h7252, h7253, h7850, h7854, h7856, h7860, hlam]
                                    · rcases h1bigk with h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c | h7862c
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h0, hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h6137, hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7253, h7801, h7850, h7851, h7856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7253, hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7801, hc01, hc23, hlam, hphi, ht12, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7801, hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7801, h7850, h7856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7801, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7252, h7801, h7850, h7856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7801, hc12, hc23, hlam, hphi, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        rcases p7862_3 (m.d 0 1) (by simp) with h7876 | h7876
                                        · linarith only [h6137, h7876, hlam]
                                        · linarith only [h7252, h7876, hlam]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7252, h7253, h7801, h7850, h7856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7252, hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7850, hlam, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7852, hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7854, hlam, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7252, h7850, h7851, h7856, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7851, hlam, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7853, hlam, p7862_0]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [h7801, h7850, h7851, h7856, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7862_1]
                                      · have p7862_0 := h7862c.1
                                        have p7862_1 := h7862c.2.1
                                        have p7862_2 := h7862c.2.2.1
                                        have p7862_3 := h7862c.2.2.2
                                        linarith only [hlam, p7862_0]
                                · linarith only [h0, h7252, h7801, h7850, h7856, h7857, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h7253, h7801, h7851, h7856, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h0, h6137, h7252, h7796, h7798, h7801, h7850, h7853, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h6137, h7797, h7852, hlam]
                      · linarith only [h0, h7252, h7796, h7850, h7851, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7795, h7850, hlam]
              · linarith only [h7604, h7796, h7798, hlam]
            · linarith only [h0, h7252, h7604, h7797, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h7898 | h7898
            · rcases m.htr 0 3 5 (by decide) (by decide) with h7899 | h7899
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7900 | h7900
                · linarith only [h0, h7252, h7796, h7900, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7902 | h7902
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7903 | h7903
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7904 | h7904
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7905 | h7905
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7906 | h7906
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7907 | h7907
                            · linarith only [h0, h7252, h7604, h7900, h7902, h7907, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7909 | h7909
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7910 | h7910
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7911 | h7911
                                  · linarith only [h0, h7252, h7796, h7902, h7903, h7907, h7910, h7911, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7913 | h7913
                                    · linarith only [h0, h7252, h7796, h7903, h7904, h7907, h7909, h7913, hlam]
                                    · rcases h1bigk with h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c | h7915c
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h0, hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h6137, hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h0, h7796, h7902, h7910, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7253, hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [hc01, hc12, hlam, hphi, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h6137, hc01, hc12, hlam, hphi, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        rcases p7915_3 (m.d 0 1) (by simp) with h7924 | h7924
                                        · linarith only [h0, h7924, hlam]
                                        · linarith only [h7252, h7924, hlam]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7796, h7904, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7252, h7903, h7909, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7902, hlam, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        rcases p7915_3 (m.d 0 1) (by simp) with h7931 | h7931
                                        · linarith only [h6137, h7931, hlam]
                                        · linarith only [h7252, h7931, hlam]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h0, h7252, h7796, h7902, h7903, h7904, h7909, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7252, hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7903, hlam, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7905, hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7907, hlam, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7252, h7903, h7909, hc15, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7904, hlam, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7906, hlam, p7915_0]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [h7903, h7907, h7909, hc34, hc45, hlam, hphi, p7915_1]
                                      · have p7915_0 := h7915c.1
                                        have p7915_1 := h7915c.2.1
                                        have p7915_2 := h7915c.2.2.1
                                        have p7915_3 := h7915c.2.2.2
                                        linarith only [hlam, p7915_0]
                                · linarith only [h0, h6137, h7252, h7604, h7899, h7902, h7903, h7909, h7910, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h7252, h7604, h7898, h7903, h7909, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h6137, h7899, h7906, hlam]
                        · linarith only [h7604, h7898, h7902, h7905, hlam]
                      · linarith only [h0, h7252, h7604, h7902, h7903, h7904, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h7252, h7604, h7902, h7903, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7951 | h7951
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7952 | h7952
                      · linarith only [h0, h7252, h7796, h7902, h7951, h7952, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7954 | h7954
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7955 | h7955
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7956 | h7956
                            · linarith only [h0, h7252, h7900, h7902, h7956, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7958 | h7958
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7959 | h7959
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7960 | h7960
                                  · linarith only [h0, h7252, h7951, h7952, h7956, h7959, h7960, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                  · linarith only [h0, h7252, h7951, h7952, h7958, h7960, hc34, hc45, hlam, hphi]
                                · linarith only [h6137, h7899, h7902, h7959, hlam]
                              · linarith only [h6137, h7252, h7898, h7902, h7958, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · linarith only [h6137, h7899, h7955, hlam]
                        · linarith only [h6137, h7898, h7954, hlam]
                    · linarith only [h0, h7252, h7795, h7951, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7968 | h7968
                · linarith only [h7252, h7253, h7968, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h7970 | h7970
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7971 | h7971
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7972 | h7972
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7973 | h7973
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h7974 | h7974
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7975 | h7975
                            · linarith only [h0, h7252, h7604, h7968, h7975, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7977 | h7977
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7978 | h7978
                                · linarith only [h0, h7604, h7899, h7970, h7978, hc01, hc12, hlam, hphi]
                                · linarith only [h0, h7252, h7604, h7970, h7971, h7974, h7977, h7978, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h7252, h7604, h7898, h7899, h7977, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h7982 | h7982
                            · linarith only [h6137, h7252, h7974, h7982, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h7984 | h7984
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h7985 | h7985
                                · linarith only [h7970, h7974, h7985, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h7987 | h7987
                                  · linarith only [h0, h7252, h7604, h7970, h7971, h7974, h7982, h7987, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7989 | h7989
                                    · linarith only [h0, h7252, h7604, h7970, h7971, h7974, h7982, h7984, h7989, hlam]
                                    · linarith only [h0, h7252, h7604, h7970, h7971, h7974, h7984, h7989, hc34, hc45, hlam, hphi]
                              · linarith only [h0, h7252, h7604, h7898, h7971, h7984, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h7252, h7604, h7898, h7970, h7973, hlam]
                      · linarith only [h0, h7252, h7604, h7970, h7971, h7972, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h7252, h7604, h7970, h7971, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h7996 | h7996
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h7997 | h7997
                      · linarith only [h0, h7252, h7796, h7970, h7996, h7997, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h7999 | h7999
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h8000 | h8000
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h8001 | h8001
                            · linarith only [h0, h7252, h7604, h7899, h8000, h8001, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h8003 | h8003
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h8004 | h8004
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h8005 | h8005
                                  · linarith only [h0, h7252, h7604, h7899, h7996, h8000, h8001, h8005, hlam]
                                  · linarith only [h0, h7252, h7997, h8005, hc14, hc45, hlam, hphi]
                                · linarith only [h7970, h8000, h8004, hlam]
                              · linarith only [h0, h7252, h7604, h7899, h7970, h7996, h8000, h8003, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h8010 | h8010
                            · linarith only [h0, h7252, h7970, h8000, h8010, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h8012 | h8012
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h8013 | h8013
                                · linarith only [h0, h7252, h7970, h7996, h8000, h8012, h8013, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h0, h7252, h7970, h7996, h8012, h8013, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                              · linarith only [h0, h7252, h7970, h7996, h8012, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h7252, h7898, h7970, h7996, h7999, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h7795, h7996, hlam]
            · linarith only [h6137, h7252, h7898, hlam]
        · linarith only [h0, h7252, h7795, hlam]
  · exact r1l7_21_15_H_I_L_I_s9 m hb1 hb5 h0 h6137 h7252

end R2N4
