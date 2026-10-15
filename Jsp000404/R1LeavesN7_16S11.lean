import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_16S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8694 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8695 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8696 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 3 5 (by decide) (by decide) with h9255 | h9255
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9256 | h9256
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9257 | h9257
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9258 | h9258
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9259 | h9259
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9260 | h9260
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9261 | h9261
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9262 | h9262
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9263 | h9263
                  · linarith only [h8693, h8696, h9263, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9265 | h9265
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9266 | h9266
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9267 | h9267
                        · rcases h1bigk with h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h0, hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h6137, hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h7252, hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h8021, hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h8696, h9260, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h8693, h8696, h9260, h9265, h9267, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h9257, hlam, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h8693, h8696, h9257, h9260, h9265, h9267, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h8021, h9257, hc01, hc12, hlam, hphi, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h9258, hlam, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h9260, hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h8021, h9257, h9260, hc01, hc12, hlam, hphi, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h9259, hlam, p9268_1]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h9261, hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [h9262, hlam, p9268_0]
                          · have p9268_0 := h9268c.1
                            have p9268_1 := h9268c.2.1
                            have p9268_2 := h9268c.2.2.1
                            have p9268_3 := h9268c.2.2.2
                            linarith only [hlam, p9268_0]
                        · linarith only [h6137, h7252, h8696, h9256, h9257, h9260, h9267, hc01, hc12, hlam, hphi]
                      · linarith only [h8696, h9255, h9256, h9257, h9260, h9263, h9265, h9266, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h8696, h9255, h9257, h9260, h9265, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h7252, h8696, h9255, h9256, h9257, h9260, h9262, hc01, hc12, hlam, hphi]
              · linarith only [h8696, h9255, h9260, h9261, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9299 | h9299
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9300 | h9300
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9301 | h9301
                  · linarith only [h6137, h9260, h9301, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9303 | h9303
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9304 | h9304
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9305 | h9305
                        · rcases h1bigk with h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c | h9306c
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h0, hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h6137, hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h7252, hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h8021, hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h8021, h9299, hc01, hc12, hlam, hphi, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h9257, hlam, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h9260, hlam, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h8021, hc01, hc13, hlam, hphi, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h9258, hlam, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h6137, hc01, hc14, hlam, hphi, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h8021, h9260, hc01, hc34, hlam, hphi, ht12, ht23, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h9299, hc01, hc13, hlam, hphi, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h9259, hlam, p9306_1]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h9299, hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [h9300, hlam, p9306_0]
                          · have p9306_0 := h9306c.1
                            have p9306_1 := h9306c.2.1
                            have p9306_2 := h9306c.2.2.1
                            have p9306_3 := h9306c.2.2.2
                            linarith only [hlam, p9306_0]
                        · linarith only [h6137, h9260, h9305, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h9301, h9303, h9304, hlam]
                    · linarith only [h6137, h9255, h9260, h9303, hc23, hc34, hlam, hphi]
                · linarith only [h6137, h7252, h9255, h9256, h9260, h9300, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h6137, h9255, h9299, hlam]
          · linarith only [h0, h8695, h9259, hlam]
        · linarith only [h0, h8694, h9258, hlam]
      · linarith only [h0, h8693, h9257, hlam]
    · linarith only [h8696, h9255, h9256, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9341 | h9341
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9342 | h9342
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9343 | h9343
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9344 | h9344
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9345 | h9345
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9346 | h9346
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9347 | h9347
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9348 | h9348
                  · linarith only [h8693, h8696, h9348, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9350 | h9350
                    · linarith only [h8693, h9255, h9350, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9352 | h9352
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9353 | h9353
                        · rcases h1bigk with h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h0, hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h6137, hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h7252, hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h8021, hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h6137, h9255, h9345, h9353, hc01, hc12, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h6137, h9255, h9346, h9347, hc01, hc12, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h6137, h9255, h9346, hc01, hc12, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h9342, hlam, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h6137, h9255, h9342, h9346, h9347, hc01, hc12, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h6137, h9255, h9342, h9346, hc01, hc12, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h9343, hlam, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h9345, hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h6137, h9255, h9342, h9345, h9346, hc01, hc12, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h9344, hlam, p9354_1]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h9346, hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [h9347, hlam, p9354_0]
                          · have p9354_0 := h9354c.1
                            have p9354_1 := h9354c.2.1
                            have p9354_2 := h9354c.2.2.1
                            have p9354_3 := h9354c.2.2.2
                            linarith only [hlam, p9354_0]
                        · linarith only [h8694, h8696, h9352, h9353, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9381 | h9381
                        · rcases h1bigk with h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c | h9382c
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h0, hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h6137, hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h7252, hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h8021, hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h7252, h9341, h9348, h9352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h9342, hlam, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h7252, h9341, h9342, h9348, h9352, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h8021, h9342, hc01, hc12, hlam, hphi, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h9343, hlam, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h9345, hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h6137, h9255, h9342, h9345, h9346, hc01, hc12, hlam, hphi, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h9344, hlam, p9382_1]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h9346, hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [h9347, hlam, p9382_0]
                          · have p9382_0 := h9382c.1
                            have p9382_1 := h9382c.2.1
                            have p9382_2 := h9382c.2.2.1
                            have p9382_3 := h9382c.2.2.2
                            linarith only [hlam, p9382_0]
                        · linarith only [h8696, h9341, h9381, hlam]
                · linarith only [h7252, h8696, h9341, h9347, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h6137, h8696, h9345, h9346, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9411 | h9411
              · linarith only [h6137, h9255, h9345, h9411, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9413 | h9413
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9414 | h9414
                  · linarith only [h6137, h9345, h9414, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9416 | h9416
                    · linarith only [h8693, h9255, h9416, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9418 | h9418
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9419 | h9419
                        · rcases h1bigk with h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c | h9420c
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [hlam, p9420_0]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h0, hlam, p9420_0]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h6137, hlam, p9420_0]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h7252, hlam, p9420_0]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h8021, hlam, p9420_0]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [hlam, p9420_0]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h7252, hc01, hc12, hlam, hphi, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h9342, hlam, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [hlam, p9420_0]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h9345, hlam, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h9411, hlam, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h9343, hlam, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h9345, hc13, hc34, hlam, hphi, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [hlam, p9420_0]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h8021, h9345, hc01, hc34, hlam, hphi, ht12, ht23, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h9344, hlam, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h6137, h9411, h9419, hc01, hc34, hlam, hphi, ht12, ht23, p9420_1]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [h9413, hlam, p9420_0]
                          · have p9420_0 := h9420c.1
                            have p9420_1 := h9420c.2.1
                            have p9420_2 := h9420c.2.2.1
                            have p9420_3 := h9420c.2.2.2
                            linarith only [hlam, p9420_0]
                        · linarith only [h7252, h9341, h9345, h9419, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9447 | h9447
                        · rcases h1bigk with h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c | h9448c
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [hlam, p9448_0]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h0, hlam, p9448_0]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h6137, hlam, p9448_0]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h7252, hlam, p9448_0]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h8021, hlam, p9448_0]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [hlam, p9448_0]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h7252, h9341, h9414, h9418, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h9342, hlam, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [hlam, p9448_0]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h9345, hlam, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h9411, hlam, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h9343, hlam, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h9345, hc13, hc34, hlam, hphi, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [hlam, p9448_0]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h6137, h9345, h9411, hc01, hc34, hlam, hphi, ht12, ht23, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h9344, hlam, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h6137, h9411, hc01, hc35, hlam, hphi, ht12, ht23, p9448_1]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [h9413, hlam, p9448_0]
                          · have p9448_0 := h9448c.1
                            have p9448_1 := h9448c.2.1
                            have p9448_2 := h9448c.2.2.1
                            have p9448_3 := h9448c.2.2.2
                            linarith only [hlam, p9448_0]
                        · linarith only [h7252, h9341, h9345, h9447, hlam]
                · linarith only [h7252, h9341, h9413, hlam]
          · linarith only [h0, h8694, h8695, h9341, h9344, hlam]
        · linarith only [h0, h8694, h9343, hlam]
      · linarith only [h0, h8693, h9342, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9479 | h9479
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9480 | h9480
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9481 | h9481
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9482 | h9482
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9483 | h9483
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9484 | h9484
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9485 | h9485
                  · linarith only [h8693, h8696, h9485, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9487 | h9487
                    · linarith only [h8021, h8693, h8696, h9255, h9341, h9479, h9482, h9484, h9487, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9489 | h9489
                      · linarith only [h8694, h9341, h9489, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9491 | h9491
                        · linarith only [h6137, h8696, h9341, h9479, h9482, h9491, hc01, hc12, hlam, hphi]
                        · linarith only [h6137, h8696, h9479, h9482, h9484, h9491, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9494 | h9494
                  · linarith only [h8693, h8696, h9494, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9496 | h9496
                    · linarith only [h8693, h9255, h9496, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9498 | h9498
                      · linarith only [h7252, h9484, h9498, hc01, hc24, hlam, hphi, ht12]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9500 | h9500
                        · linarith only [h9482, h9484, h9500, hlam]
                        · rcases h1bigk with h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c | h9502c
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h0, hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h6137, hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h7252, hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h8021, hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h6137, h8696, h9482, hc01, hc12, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h8021, hc01, hc12, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h9479, hlam, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h6137, h8696, h9479, h9482, hc01, hc12, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h7252, h8021, h9341, h9479, hc01, hc12, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h9480, hlam, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h9482, hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h9484, hlam, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h9481, hlam, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h9483, hlam, p9502_0]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [h9484, hc14, hc45, hlam, hphi, p9502_1]
                          · have p9502_0 := h9502c.1
                            have p9502_1 := h9502c.2.1
                            have p9502_2 := h9502c.2.2.1
                            have p9502_3 := h9502c.2.2.2
                            linarith only [hlam, p9502_0]
              · linarith only [h6137, h8696, h9482, h9483, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9529 | h9529
              · linarith only [h6137, h9255, h9482, h9529, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9531 | h9531
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9532 | h9532
                  · linarith only [h8693, h8696, h9341, h9482, h9532, hc13, hc45, hlam, hphi, ht34]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9534 | h9534
                    · linarith only [h8021, h8693, h8696, h9341, h9482, h9529, h9531, h9534, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9536 | h9536
                      · linarith only [h8694, h9341, h9536, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9538 | h9538
                        · rcases h1bigk with h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c | h9539c
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [hlam, p9539_0]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h0, hlam, p9539_0]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h6137, hlam, p9539_0]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h7252, hlam, p9539_0]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h8021, hlam, p9539_0]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [hc01, hc12, hlam, hphi, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [hlam, p9539_0]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h6137, hc01, hc12, hlam, hphi, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h8696, h9341, h9531, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h6137, h8696, h9341, h9531, hc01, hc12, hlam, hphi, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [hc01, hc13, hlam, hphi, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h9479, hlam, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [hlam, p9539_0]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h9482, hlam, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h9529, hlam, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [hc01, hc14, hlam, hphi, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h9480, hlam, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h9482, hc13, hc34, hlam, hphi, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [hlam, p9539_0]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h6137, h8696, h9341, h9482, h9531, hc01, hc34, hlam, hphi, ht12, ht23, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [hc01, hc15, hlam, hphi, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h9481, hlam, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h6137, h9529, hc01, hc35, hlam, hphi, ht12, ht23, p9539_1]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [h9531, hlam, p9539_0]
                          · have p9539_0 := h9539c.1
                            have p9539_1 := h9539c.2.1
                            have p9539_2 := h9539c.2.2.1
                            have p9539_3 := h9539c.2.2.2
                            linarith only [hlam, p9539_0]
                        · linarith only [h6137, h9482, h9538, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9566 | h9566
                  · linarith only [h6137, h9482, h9566, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9568 | h9568
                    · linarith only [h8693, h9255, h9568, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9570 | h9570
                      · linarith only [h7252, h8694, h9531, h9570, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9572 | h9572
                        · linarith only [h7252, h9531, h9572, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h6137, h9482, h9572, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h8695, h9481, hlam]
        · linarith only [h0, h8694, h9480, hlam]
      · linarith only [h0, h8693, h8696, h9479, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8694 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8695 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 3 4 (by decide) (by decide) with h8696 | h8696
  · exact r1l7_21_15_H_I_L_I_s10_x0_x0_x0_x0 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h8694 h8695 h8696
  · exact r1l7_21_15_H_I_L_I_s10_x0_x0_x0_x1 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h8694 h8695 h8696

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8694 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8695 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 3 4 (by decide) (by decide) with h9578 | h9578
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9579 | h9579
    · linarith only [h8693, h8695, h9579, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9581 | h9581
      · linarith only [h8693, h8695, h9578, h9581, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9583 | h9583
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9584 | h9584
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9585 | h9585
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9586 | h9586
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9587 | h9587
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9588 | h9588
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9589 | h9589
                    · linarith only [h8693, h8695, h9585, h9589, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8693, h8695, h9578, h9585, h9589, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9592 | h9592
                    · linarith only [h8693, h8695, h9585, h9592, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8693, h8695, h9578, h9585, h9592, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9595 | h9595
                  · linarith only [h7252, h9581, h9586, h9587, h9595, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9597 | h9597
                    · linarith only [h8693, h8695, h9585, h9597, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h8693, h8695, h9578, h9585, h9597, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h6137, h8693, h8695, h9578, h9585, h9586, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9601 | h9601
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9602 | h9602
                · linarith only [h9578, h9579, h9583, h9585, h9602, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9604 | h9604
                  · linarith only [h7252, h9581, h9584, h9585, h9604, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9606 | h9606
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9607 | h9607
                      · linarith only [h0, h8693, h9585, h9602, h9607, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9609 | h9609
                        · linarith only [h8694, h9581, h9609, hlam]
                        · linarith only [h0, h8693, h9585, h9606, h9609, hc34, hc45, hlam, hphi]
                    · linarith only [h9578, h9579, h9606, hc23, hc35, hlam, hphi]
              · linarith only [h6137, h9578, h9601, hlam]
          · linarith only [h0, h8694, h9584, hlam]
        · linarith only [h0, h8693, h9583, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h9616 | h9616
    · linarith only [h8694, h8695, h9578, h9616, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h9618 | h9618
      · linarith only [h8694, h8695, h9618, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h9620 | h9620
        · rcases m.htr 1 2 4 (by decide) (by decide) with h9621 | h9621
          · rcases m.htr 1 2 5 (by decide) (by decide) with h9622 | h9622
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9623 | h9623
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9624 | h9624
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9625 | h9625
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9626 | h9626
                    · linarith only [h0, h6137, h8693, h9578, h9626, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9628 | h9628
                      · linarith only [h8694, h8695, h9616, h9622, h9626, h9628, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9630 | h9630
                        · linarith only [h8694, h8695, h9620, h9624, h9628, h9630, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9632 | h9632
                          · linarith only [h8694, h8695, h9626, h9630, h9632, hc23, hc34, hlam, hphi]
                          · linarith only [h6137, h9578, h9620, h9623, h9625, h9632, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9635 | h9635
                    · linarith only [h6137, h8693, h8695, h9578, h9635, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9637 | h9637
                      · linarith only [h8694, h8695, h9616, h9622, h9635, h9637, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9639 | h9639
                        · linarith only [h8694, h8695, h9620, h9624, h9625, h9637, h9639, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9641 | h9641
                          · linarith only [h9623, h9625, h9641, hlam]
                          · rcases h1bigk with h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c | h9643c
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h0, hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h6137, hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h7252, hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h8021, hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h8694, h8695, h9624, h9635, h9637, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h6137, h9578, h9623, hc01, hc12, hlam, hphi, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h8021, hc01, hc12, hlam, hphi, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h9620, hlam, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h6137, h9578, h9620, h9623, hc01, hc12, hlam, hphi, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h8694, h8695, h9620, h9622, h9635, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h9621, hlam, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h9623, hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h9625, hlam, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h9622, hlam, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h9624, hlam, p9643_0]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [h9625, hc14, hc45, hlam, hphi, p9643_1]
                            · have p9643_0 := h9643c.1
                              have p9643_1 := h9643c.2.1
                              have p9643_2 := h9643c.2.2.1
                              have p9643_3 := h9643c.2.2.2
                              linarith only [hlam, p9643_0]
                · linarith only [h6137, h9578, h9623, h9624, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9670 | h9670
                · linarith only [h6137, h9616, h9623, h9670, hc01, hc34, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9672 | h9672
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9673 | h9673
                    · linarith only [h8693, h8695, h9622, h9623, h9673, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9675 | h9675
                      · linarith only [h8694, h8695, h9622, h9670, h9673, h9675, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9677 | h9677
                        · linarith only [h6137, h8694, h8695, h9578, h9618, h9622, h9677, hc01, hc12, hlam, hphi]
                        · linarith only [h8694, h8695, h9623, h9672, h9673, h9677, hc23, hc34, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9680 | h9680
                    · linarith only [h8693, h8695, h9622, h9680, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9682 | h9682
                      · linarith only [h6137, h8694, h8695, h9622, h9670, h9680, h9682, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9684 | h9684
                        · linarith only [h6137, h8694, h8695, h9622, h9623, h9672, h9684, hc01, hc12, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9686 | h9686
                          · linarith only [h6137, h9623, h9672, h9686, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h6137, h9623, h9686, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h9689 | h9689
              · linarith only [h6137, h9578, h9620, h9622, h9689, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h9691 | h9691
                · linarith only [h6137, h9616, h9621, h9622, h9689, h9691, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9693 | h9693
                  · linarith only [h6137, h9578, h9618, h9621, h9622, h9693, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h9695 | h9695
                    · linarith only [h0, h8693, h9622, h9689, h9695, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h9697 | h9697
                      · linarith only [h8693, h9616, h9697, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h9699 | h9699
                        · linarith only [h7252, h9693, h9699, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h9701 | h9701
                          · linarith only [h0, h9622, h9699, h9701, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h6137, h9689, h9701, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
          · linarith only [h0, h8694, h9621, hlam]
        · linarith only [h0, h8693, h9620, hlam]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8694 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 2 5 (by decide) (by decide) with h8695 | h8695
  · exact r1l7_21_15_H_I_L_I_s10_x0_x0_x0 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h8694 h8695
  · exact r1l7_21_15_H_I_L_I_s10_x0_x0_x1 m hb1 hb5 hg0 hg6137 hg7252 hg8021 h8693 h8694 h8695

end R2N4
