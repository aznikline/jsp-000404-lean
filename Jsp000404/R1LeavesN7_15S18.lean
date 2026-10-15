import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10280000 in
set_option maxHeartbeats 10280000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s7_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6253 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h6254 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h6255 | h6255
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6256 | h6256
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6257 | h6257
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6258 | h6258
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6259 | h6259
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6260 | h6260
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6261 | h6261
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6262 | h6262
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6263 | h6263
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6264 | h6264
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6265 | h6265
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6266 | h6266
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6267 | h6267
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6268 | h6268
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6269 | h6269
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6270 | h6270
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6271 | h6271
                                  · linarith only [h0, h6253, h6262, h6268, h6271, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h6253, h6265, h6267, h6271, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h6253, h6265, h6267, h6270, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h6253, h6266, h6269, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h6253, h6265, h6268, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6277 | h6277
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6278 | h6278
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6279 | h6279
                                · linarith only [h6263, h6267, h6279, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6281 | h6281
                                  · linarith only [h6256, h6267, h6277, h6281, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c | h6283c
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [hlam, p6283_0]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, hlam, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [hlam, p6283_0]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, h6253, h6262, h6278, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, h6261, h6263, h6267, h6277, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, h6261, h6263, h6267, h6277, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6253, hlam, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6256, hlam, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [hlam, p6283_0]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6253, h6261, h6263, h6267, h6277, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, h6253, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6254, hlam, p6283_0]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6257, hlam, p6283_0]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6259, hlam, p6283_0]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [hlam, p6283_0]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h0, h6254, h6255, h6264, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6255, hlam, p6283_0]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6258, hlam, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6260, hlam, p6283_0]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [h6261, hlam, p6283_1]
                                    · have p6283_0 := h6283c.1
                                      have p6283_1 := h6283c.2.1
                                      have p6283_2 := h6283c.2.2.1
                                      have p6283_3 := h6283c.2.2.2
                                      linarith only [hlam, p6283_0]
                              · linarith only [h0, h6253, h6260, h6277, h6278, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h6253, h6265, h6277, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h6253, h6260, h6265, h6266, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6312 | h6312
                        · linarith only [h0, h6253, h6259, h6265, h6312, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6314 | h6314
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6315 | h6315
                            · linarith only [h6262, h6265, h6315, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6317 | h6317
                              · linarith only [h6262, h6312, h6317, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6319 | h6319
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6320 | h6320
                                  · rcases h0bigk with h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c | h6321c
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [hlam, p6321_0]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h0, hlam, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [hlam, p6321_0]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h0, h6259, h6312, h6320, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h0, h6254, h6263, h6319, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h0, h6260, h6312, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6253, hlam, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6256, hlam, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [hlam, p6321_0]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6253, h6259, h6312, h6320, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h0, h6253, h6260, h6312, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6254, hlam, p6321_0]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6257, hlam, p6321_0]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6259, hlam, p6321_0]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [hlam, p6321_0]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6260, h6312, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6255, hlam, p6321_0]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6258, hlam, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6260, hlam, p6321_0]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [h6261, hlam, p6321_1]
                                    · have p6321_0 := h6321c.1
                                      have p6321_1 := h6321c.2.1
                                      have p6321_2 := h6321c.2.2.1
                                      have p6321_3 := h6321c.2.2.2
                                      linarith only [hlam, p6321_0]
                                  · linarith only [h0, h6254, h6263, h6319, h6320, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h6253, h6259, h6265, h6314, h6319, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6349 | h6349
                            · linarith only [h0, h6253, h6260, h6262, h6312, h6349, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6351 | h6351
                              · linarith only [h0, h6253, h6259, h6261, h6262, h6265, h6314, h6351, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6353 | h6353
                                · linarith only [h6263, h6314, h6353, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6355 | h6355
                                  · linarith only [h0, h6253, h6259, h6314, h6355, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h6253, h6259, h6261, h6262, h6265, h6355, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6258, h6264, hlam]
                  · linarith only [h0, h6257, h6263, hlam]
                · linarith only [h0, h6256, h6262, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6361 | h6361
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6362 | h6362
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6363 | h6363
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6364 | h6364
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6365 | h6365
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6366 | h6366
                          · linarith only [h0, h6253, h6261, h6364, h6366, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6368 | h6368
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6369 | h6369
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6370 | h6370
                                · linarith only [h6254, h6261, h6362, h6370, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6372 | h6372
                                  · linarith only [h0, h6253, h6261, h6361, h6368, h6372, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c | h6374c
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h0, hlam, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h0, h6254, h6362, h6368, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h0, h6253, h6361, h6369, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      rcases p6374_3 (m.d 0 1) (by simp) with h6383 | h6383
                                      · linarith only [h0, h6383, hlam]
                                      · linarith only [h6254, h6383, hlam]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      rcases p6374_3 (m.d 0 1) (by simp) with h6386 | h6386
                                      · linarith only [h0, h6386, hlam]
                                      · linarith only [h6255, h6386, hlam]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h6253, hlam, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h6256, hlam, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h0, h6253, h6254, h6362, h6368, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h0, h6253, h6254, h6261, h6362, h6368, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h6254, hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h6257, hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h6259, hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h6261, hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h6255, hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h6258, hlam, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h6260, hlam, p6374_0]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [h0, h6254, h6255, h6362, h6368, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6374_1]
                                    · have p6374_0 := h6374c.1
                                      have p6374_1 := h6374c.2.1
                                      have p6374_2 := h6374c.2.2.1
                                      have p6374_3 := h6374c.2.2.2
                                      linarith only [hlam, p6374_0]
                              · linarith only [h0, h6253, h6365, h6369, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h6253, h6364, h6368, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h6253, h6260, h6364, h6365, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6407 | h6407
                        · linarith only [h0, h6253, h6259, h6364, h6407, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6409 | h6409
                          · linarith only [h0, h6254, h6261, h6409, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6411 | h6411
                            · linarith only [h6361, h6364, h6411, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6413 | h6413
                              · linarith only [h6257, h6261, h6407, h6411, h6413, hc13, hc45, hlam, hphi, ht34]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6415 | h6415
                                · linarith only [h0, h6254, h6261, h6362, h6415, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6417 | h6417
                                  · linarith only [h6259, h6261, h6417, hlam]
                                  · rcases h0bigk with h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c | h6419c
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h0, hlam, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h0, h6260, h6361, h6364, h6417, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h0, h6259, h6361, h6364, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h0, h6260, h6361, h6364, h6417, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h0, h6259, h6361, h6364, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h0, h6260, h6361, h6364, h6417, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6253, hlam, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6256, hlam, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6253, h6259, h6361, h6364, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h0, h6253, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6254, hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6257, hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6259, hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6261, hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6255, hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6258, hlam, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6260, hlam, p6419_0]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [h6259, h6361, h6364, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6419_1]
                                    · have p6419_0 := h6419c.1
                                      have p6419_1 := h6419c.2.1
                                      have p6419_2 := h6419c.2.2.1
                                      have p6419_3 := h6419c.2.2.2
                                      linarith only [hlam, p6419_0]
                    · linarith only [h0, h6258, h6363, hlam]
                  · linarith only [h0, h6257, h6362, hlam]
                · linarith only [h0, h6256, h6361, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6448 | h6448
              · linarith only [h6259, h6260, h6448, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6450 | h6450
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6451 | h6451
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6452 | h6452
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6453 | h6453
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6454 | h6454
                        · linarith only [h0, h6253, h6260, h6454, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6456 | h6456
                          · linarith only [h0, h6254, h6448, h6456, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6458 | h6458
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6459 | h6459
                              · linarith only [h6256, h6260, h6459, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6461 | h6461
                                · linarith only [h0, h6254, h6255, h6448, h6450, h6454, h6458, h6461, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6463 | h6463
                                  · linarith only [h6259, h6260, h6448, h6463, hlam]
                                  · rcases h0bigk with h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c | h6465c
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [hlam, p6465_0]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h0, hlam, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h0, h6254, h6451, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h0, h6253, h6260, h6450, h6458, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [hlam, p6465_0]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h0, h6253, h6450, h6458, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      rcases p6465_3 (m.d 0 1) (by simp) with h6474 | h6474
                                      · linarith only [h0, h6474, hlam]
                                      · linarith only [h6254, h6474, hlam]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h0, h6253, h6260, h6450, h6458, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6253, hlam, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6256, hlam, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [hlam, p6465_0]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6254, h6260, h6451, h6458, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6260, hlam, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6254, hlam, p6465_0]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6257, hlam, p6465_0]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6259, hlam, p6465_0]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [hlam, p6465_0]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6448, hlam, p6465_0]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6255, hlam, p6465_0]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6258, hlam, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h6253, h6450, h6458, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [h0, h6254, h6255, h6451, h6458, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6465_1]
                                    · have p6465_0 := h6465c.1
                                      have p6465_1 := h6465c.2.1
                                      have p6465_2 := h6465c.2.2.1
                                      have p6465_3 := h6465c.2.2.2
                                      linarith only [hlam, p6465_0]
                            · linarith only [h6259, h6260, h6458, hc23, hc35, hlam, hphi]
                      · linarith only [h6259, h6260, h6453, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h6258, h6452, hlam]
                  · linarith only [h0, h6257, h6451, hlam]
                · linarith only [h0, h6256, h6450, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6498 | h6498
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6499 | h6499
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6500 | h6500
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6501 | h6501
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6502 | h6502
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6503 | h6503
                      · linarith only [h6253, h6259, h6503, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6505 | h6505
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6506 | h6506
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6507 | h6507
                            · linarith only [h6253, h6259, h6500, h6507, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6509 | h6509
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6510 | h6510
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6511 | h6511
                                  · rcases h0bigk with h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c | h6512c
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [hlam, p6512_0]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h0, hlam, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [hlam, p6512_0]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h0, h6253, h6500, h6509, h6511, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h0, h6253, h6259, h6500, h6509, h6511, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      rcases p6512_3 (m.d 0 1) (by simp) with h6522 | h6522
                                      · linarith only [h0, h6522, hlam]
                                      · linarith only [h6255, h6522, hlam]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6253, hlam, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6256, hlam, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [hlam, p6512_0]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6259, hlam, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6255, h6259, h6502, h6509, h6511, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6254, hlam, p6512_0]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6257, hlam, p6512_0]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6253, h6500, h6509, h6511, hc04, hc45, hlam, hphi, ht0b, ht5b, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [hlam, p6512_0]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h0, h6254, h6255, h6502, h6509, h6511, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6255, hlam, p6512_0]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6258, hlam, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6498, hlam, p6512_0]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [h6499, hlam, p6512_1]
                                    · have p6512_0 := h6512c.1
                                      have p6512_1 := h6512c.2.1
                                      have p6512_2 := h6512c.2.2.1
                                      have p6512_3 := h6512c.2.2.2
                                      linarith only [hlam, p6512_0]
                                  · linarith only [h6253, h6259, h6499, h6500, h6509, h6511, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h6254, h6506, h6510, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h6259, h6498, h6509, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h6254, h6499, h6503, h6505, h6506, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h6259, h6498, h6500, h6505, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h6258, h6502, hlam]
                  · linarith only [h0, h6257, h6501, hlam]
                · linarith only [h0, h6256, h6500, hlam]
              · linarith only [h6259, h6498, h6499, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6549 | h6549
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6550 | h6550
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6551 | h6551
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6552 | h6552
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6553 | h6553
                      · linarith only [h0, h6253, h6259, h6553, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6555 | h6555
                        · linarith only [h6253, h6498, h6555, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6557 | h6557
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6558 | h6558
                            · linarith only [h6256, h6259, h6558, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6560 | h6560
                              · linarith only [h6253, h6498, h6550, h6560, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6562 | h6562
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6563 | h6563
                                  · rcases h0bigk with h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c | h6564c
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [hlam, p6564_0]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h0, hlam, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [hlam, p6564_0]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      rcases p6564_3 (m.d 0 1) (by simp) with h6572 | h6572
                                      · linarith only [h0, h6572, hlam]
                                      · linarith only [h6253, h6572, hlam]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h0, h6254, h6551, h6562, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      rcases p6564_3 (m.d 0 1) (by simp) with h6576 | h6576
                                      · linarith only [h0, h6576, hlam]
                                      · linarith only [h6255, h6576, hlam]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h6253, hlam, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h6256, hlam, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [hlam, p6564_0]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h6259, hlam, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h6498, hlam, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h6254, hlam, p6564_0]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h6257, hlam, p6564_0]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h0, h6253, h6254, h6550, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [hlam, p6564_0]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h0, h6253, h6254, h6498, h6550, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h6255, hlam, p6564_0]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h6258, hlam, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h0, h6253, h6255, h6550, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [h6549, hlam, p6564_1]
                                    · have p6564_0 := h6564c.1
                                      have p6564_1 := h6564c.2.1
                                      have p6564_2 := h6564c.2.2.1
                                      have p6564_3 := h6564c.2.2.2
                                      linarith only [hlam, p6564_0]
                                  · linarith only [h0, h6254, h6259, h6551, h6562, h6563, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h6254, h6557, h6562, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6596 | h6596
                            · linarith only [h6259, h6549, h6550, h6553, h6557, h6596, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6598 | h6598
                              · linarith only [h6498, h6549, h6550, h6553, h6557, h6598, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6600 | h6600
                                · linarith only [h6551, h6557, h6600, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6602 | h6602
                                  · rcases h0bigk with h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c | h6603c
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [hlam, p6603_0]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h0, hlam, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h0, h6253, h6550, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h0, h6549, h6550, h6553, h6557, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h0, h6549, h6550, h6553, h6557, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [hlam, p6603_0]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      rcases p6603_3 (m.d 0 1) (by simp) with h6611 | h6611
                                      · linarith only [h0, h6611, hlam]
                                      · linarith only [h6253, h6611, hlam]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h0, h6549, h6550, h6553, h6557, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h0, h6549, h6550, h6553, h6557, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6253, hlam, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6256, hlam, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [hlam, p6603_0]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6259, hlam, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6498, hlam, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6254, hlam, p6603_0]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6257, hlam, p6603_0]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6253, h6259, h6550, hc23, hc34, hlam, hphi, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [hlam, p6603_0]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h0, h6254, h6549, h6550, h6553, h6557, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6255, hlam, p6603_0]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6258, hlam, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6253, h6498, h6550, hc23, hc35, hlam, hphi, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [h6549, hlam, p6603_1]
                                    · have p6603_0 := h6603c.1
                                      have p6603_1 := h6603c.2.1
                                      have p6603_2 := h6603c.2.2.1
                                      have p6603_3 := h6603c.2.2.2
                                      linarith only [hlam, p6603_0]
                                  · linarith only [h6259, h6549, h6602, hlam]
                    · linarith only [h0, h6258, h6552, hlam]
                  · linarith only [h0, h6257, h6551, hlam]
                · linarith only [h0, h6256, h6550, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6635 | h6635
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6636 | h6636
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6637 | h6637
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6638 | h6638
                      · linarith only [h6253, h6259, h6638, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6640 | h6640
                        · linarith only [h6253, h6498, h6640, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6642 | h6642
                          · linarith only [h0, h6254, h6259, h6549, h6642, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6644 | h6644
                            · linarith only [h6253, h6259, h6635, h6644, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6646 | h6646
                              · linarith only [h6253, h6498, h6635, h6646, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6648 | h6648
                                · linarith only [h6254, h6549, h6636, h6648, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6650 | h6650
                                  · rcases h0bigk with h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c | h6651c
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h0, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h0, h6253, h6635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h0, h6253, h6259, h6635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h0, h6253, h6259, h6549, h6635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      rcases p6651_3 (m.d 0 1) (by simp) with h6659 | h6659
                                      · linarith only [h0, h6659, hlam]
                                      · linarith only [h6253, h6659, hlam]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      rcases p6651_3 (m.d 0 1) (by simp) with h6662 | h6662
                                      · linarith only [h0, h6662, hlam]
                                      · linarith only [h6254, h6662, hlam]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      rcases p6651_3 (m.d 0 1) (by simp) with h6665 | h6665
                                      · linarith only [h0, h6665, hlam]
                                      · linarith only [h6255, h6665, hlam]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6253, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6256, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6259, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6498, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6254, hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6257, hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6253, h6549, h6635, h6650, hc23, hc34, hlam, hphi, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6549, hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6255, hlam, p6651_0]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6258, hlam, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h0, h6253, h6255, h6635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [h6549, h6650, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p6651_1]
                                    · have p6651_0 := h6651c.1
                                      have p6651_1 := h6651c.2.1
                                      have p6651_2 := h6651c.2.2.1
                                      have p6651_3 := h6651c.2.2.2
                                      linarith only [hlam, p6651_0]
                                  · rcases h0bigk with h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c | h6683c
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [hlam, p6683_0]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h0, hlam, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h0, h6253, h6259, h6635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [hlam, p6683_0]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      rcases p6683_3 (m.d 0 1) (by simp) with h6691 | h6691
                                      · linarith only [h0, h6691, hlam]
                                      · linarith only [h6253, h6691, hlam]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      rcases p6683_3 (m.d 0 1) (by simp) with h6694 | h6694
                                      · linarith only [h0, h6694, hlam]
                                      · linarith only [h6254, h6694, hlam]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      rcases p6683_3 (m.d 0 1) (by simp) with h6697 | h6697
                                      · linarith only [h0, h6697, hlam]
                                      · linarith only [h6255, h6697, hlam]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6253, hlam, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6256, hlam, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [hlam, p6683_0]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6259, hlam, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6498, hlam, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6254, hlam, p6683_0]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6257, hlam, p6683_0]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h0, h6253, h6254, h6635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [hlam, p6683_0]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6549, hlam, p6683_0]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6255, hlam, p6683_0]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6258, hlam, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6253, h6498, h6635, hc23, hc35, hlam, hphi, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [h6549, hc04, hc45, hlam, hphi, p6683_1]
                                    · have p6683_0 := h6683c.1
                                      have p6683_1 := h6683c.2.1
                                      have p6683_2 := h6683c.2.2.1
                                      have p6683_3 := h6683c.2.2.2
                                      linarith only [hlam, p6683_0]
                    · linarith only [h0, h6258, h6637, hlam]
                  · linarith only [h0, h6257, h6636, hlam]
                · linarith only [h0, h6256, h6635, hlam]
        · linarith only [h0, h6255, h6258, hlam]
      · linarith only [h0, h6254, h6257, hlam]
    · linarith only [h0, h6253, h6256, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6721 | h6721
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6722 | h6722
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6723 | h6723
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6724 | h6724
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6725 | h6725
            · linarith only [h6253, h6255, h6725, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6727 | h6727
              · linarith only [h6253, h6255, h6724, h6727, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6729 | h6729
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6730 | h6730
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6731 | h6731
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6732 | h6732
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6733 | h6733
                        · linarith only [h6253, h6255, h6725, h6731, h6733, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6735 | h6735
                          · linarith only [h6254, h6255, h6727, h6735, hlam]
                          · linarith only [h6253, h6255, h6732, h6735, hc34, hc45, hlam, hphi]
                      · linarith only [h6724, h6725, h6729, h6732, hc23, hc35, hlam, hphi]
                    · linarith only [h0, h6254, h6723, h6731, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h6722, h6730, hlam]
                · linarith only [h0, h6721, h6729, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6742 | h6742
            · linarith only [h6254, h6255, h6724, h6742, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6744 | h6744
              · linarith only [h6254, h6255, h6744, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6746 | h6746
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6747 | h6747
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6748 | h6748
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6749 | h6749
                      · linarith only [h6253, h6255, h6724, h6749, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6751 | h6751
                        · linarith only [h6253, h6255, h6742, h6751, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6753 | h6753
                          · linarith only [h6254, h6255, h6724, h6744, h6751, h6753, hc03, hc35, hlam, hphi]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6755 | h6755
                            · linarith only [h6253, h6255, h6746, h6753, h6755, hc34, hc45, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6757 | h6757
                              · linarith only [h6254, h6255, h6742, h6746, h6749, h6753, h6757, hc03, hc45, hlam, hphi, ht34]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6759 | h6759
                                · linarith only [h6254, h6255, h6747, h6753, h6759, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6761 | h6761
                                  · linarith only [h6253, h6255, h6746, h6753, h6761, hc23, hc34, hlam, hphi]
                                  · rcases h0bigk with h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c | h6763c
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [hlam, p6763_0]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h0, hlam, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6253, h6255, h6746, h6748, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6255, h6748, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6255, hlam, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h0, hc01, hc12, hlam, hphi, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [hlam, p6763_0]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      rcases p6763_3 (m.d 0 1) (by simp) with h6771 | h6771
                                      · linarith only [h0, h6771, hlam]
                                      · linarith only [h6253, h6771, hlam]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      rcases p6763_3 (m.d 0 1) (by simp) with h6774 | h6774
                                      · linarith only [h0, h6774, hlam]
                                      · linarith only [h6254, h6774, hlam]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h0, h6254, h6255, h6746, h6749, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6253, hlam, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6721, hlam, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [hlam, p6763_0]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6724, hlam, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6742, hlam, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6254, hlam, p6763_0]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6722, hlam, p6763_0]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h0, h6253, h6254, h6746, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [hlam, p6763_0]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6744, hlam, p6763_0]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6253, h6746, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6723, hlam, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6253, h6255, h6746, h6751, h6761, hc23, hc45, hlam, hphi, ht34, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [h6255, h6751, h6761, hc04, hc45, hlam, hphi, p6763_1]
                                    · have p6763_0 := h6763c.1
                                      have p6763_1 := h6763c.2.1
                                      have p6763_2 := h6763c.2.2.1
                                      have p6763_3 := h6763c.2.2.2
                                      linarith only [hlam, p6763_0]
                    · linarith only [h0, h6723, h6748, hlam]
                  · linarith only [h0, h6722, h6747, hlam]
                · linarith only [h0, h6253, h6721, h6746, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6796 | h6796
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6797 | h6797
            · linarith only [h6253, h6255, h6797, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6799 | h6799
              · linarith only [h0, h6254, h6723, h6799, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6801 | h6801
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6802 | h6802
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6803 | h6803
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6804 | h6804
                      · linarith only [h0, h6253, h6723, h6803, h6804, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h6253, h6723, h6796, h6803, h6804, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6807 | h6807
                      · linarith only [h0, h6253, h6803, h6807, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h6253, h6796, h6801, h6803, h6807, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h6253, h6722, h6723, h6796, h6802, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h6253, h6721, h6801, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6812 | h6812
            · linarith only [h6254, h6255, h6796, h6812, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6814 | h6814
              · linarith only [h0, h6254, h6723, h6814, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6816 | h6816
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6817 | h6817
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6818 | h6818
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6819 | h6819
                      · linarith only [h0, h6253, h6796, h6819, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6821 | h6821
                        · linarith only [h0, h6253, h6723, h6812, h6818, h6821, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6823 | h6823
                          · linarith only [h0, h6254, h6723, h6818, h6823, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6825 | h6825
                            · linarith only [h0, h6254, h6723, h6796, h6816, h6818, h6819, h6825, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6827 | h6827
                              · linarith only [h0, h6253, h6723, h6816, h6818, h6827, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6829 | h6829
                                · linarith only [h0, h6254, h6723, h6817, h6818, h6823, h6829, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6831 | h6831
                                  · linarith only [h0, h6254, h6723, h6816, h6818, h6819, h6823, h6831, hc23, hc34, hlam, hphi]
                                  · rcases h0bigk with h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c | h6833c
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [hlam, p6833_0]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h0, hlam, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h0, h6253, h6723, h6816, h6818, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h0, h6723, h6818, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6255, hlam, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6723, h6818, hc01, hc12, hlam, hphi, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [hlam, p6833_0]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6253, h6723, h6816, h6818, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6254, h6723, h6817, h6818, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6723, hlam, p6833_0]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6253, hlam, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6721, hlam, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [hlam, p6833_0]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6796, hlam, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6812, hlam, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6254, hlam, p6833_0]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6722, hlam, p6833_0]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h0, h6253, h6254, h6816, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [hlam, p6833_0]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6814, hlam, p6833_0]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6253, h6816, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6723, h6818, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6253, h6723, h6816, h6818, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [h6723, h6818, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6833_1]
                                    · have p6833_0 := h6833c.1
                                      have p6833_1 := h6833c.2.1
                                      have p6833_2 := h6833c.2.2.1
                                      have p6833_3 := h6833c.2.2.2
                                      linarith only [hlam, p6833_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6859 | h6859
                      · linarith only [h0, h6253, h6818, h6859, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6861 | h6861
                        · linarith only [h0, h6254, h6818, h6859, h6861, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6863 | h6863
                          · linarith only [h0, h6254, h6814, h6818, h6863, hc05, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6865 | h6865
                            · linarith only [h6253, h6796, h6816, h6865, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6867 | h6867
                              · linarith only [h0, h6254, h6816, h6818, h6859, h6861, h6867, hlam]
                              · linarith only [h0, h6254, h6816, h6818, h6859, h6867, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h6253, h6722, h6816, h6817, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6721, h6816, hlam]
      · linarith only [h0, h6254, h6722, hlam]
    · linarith only [h0, h6253, h6721, hlam]

end R2N4
