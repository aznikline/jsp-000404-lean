import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_19S9
import Jsp000404.R1LeavesN7_19S10
import Jsp000404.R1LeavesN7_19S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h6504 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h7104 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7979 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h5235 := hg5235
  rcases m.htr 0 4 5 (by decide) (by decide) with h8336 | h8336
  · rcases m.htr 1 2 3 (by decide) (by decide) with h8337 | h8337
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8338 | h8338
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8339 | h8339
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8340 | h8340
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8341 | h8341
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8342 | h8342
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8343 | h8343
                · linarith only [h5235, h7979, h8337, h8343, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8345 | h8345
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8346 | h8346
                    · rcases h1bigk with h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c | h8347c
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h0, hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h5235, hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h6110, hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h6504, hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h0, h7104, h8340, h8343, hc01, hc12, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h8337, hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h0, h7104, h8337, h8340, h8343, hc01, hc12, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h6504, h8337, hc01, hc12, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h8338, hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h8340, hlam, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h6504, h8337, h8340, hc01, hc12, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8347_1]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h8339, hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h8341, hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [h8342, hlam, p8347_0]
                      · have p8347_0 := h8347c.1
                        have p8347_1 := h8347c.2.1
                        have p8347_2 := h8347c.2.2.1
                        have p8347_3 := h8347c.2.2.2
                        linarith only [hlam, p8347_0]
                    · linarith only [h0, h6110, h7104, h8336, h8337, h8340, h8343, h8346, hc01, hc12, hlam, hphi]
                  · linarith only [h7104, h8336, h8345, hlam]
              · linarith only [h6110, h7104, h8336, h8342, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h5235, h7979, h8340, h8341, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8377 | h8377
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8378 | h8378
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8379 | h8379
                · linarith only [h5235, h7979, h8337, h8379, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8381 | h8381
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8382 | h8382
                    · rcases h1bigk with h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c | h8383c
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h0, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h5235, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h6110, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h6504, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h6504, h8377, hc01, hc12, hlam, hphi, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h0, h7104, h8338, hc01, hc12, hlam, hphi, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h8337, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h8340, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h6504, h8340, hc01, hc34, hlam, hphi, ht12, ht23, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h8338, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h8340, hc13, hc34, hlam, hphi, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h6504, h8340, hc01, hc34, hlam, hphi, ht12, ht23, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h8377, hc01, hc13, hlam, hphi, p8383_1]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h8339, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h8377, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [h8378, hlam, p8383_0]
                      · have p8383_0 := h8383c.1
                        have p8383_1 := h8383c.2.1
                        have p8383_2 := h8383c.2.2.1
                        have p8383_3 := h8383c.2.2.2
                        linarith only [hlam, p8383_0]
                    · linarith only [h5235, h7104, h8336, h8340, h8382, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h6110, h7104, h8336, h8340, h8381, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h6110, h7104, h8336, h8338, h8378, hc01, hc12, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8412 | h8412
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8413 | h8413
                · linarith only [h5235, h7979, h8337, h8413, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8415 | h8415
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8416 | h8416
                    · rcases h1bigk with h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c | h8417c
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h0, hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h5235, hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h6110, hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h6504, hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h6110, hc01, hc12, hlam, hphi, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h8337, hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h8340, hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h8377, hlam, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h8338, hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h8340, hc13, hc34, hlam, hphi, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h5235, h8340, h8377, hc01, hc34, hlam, hphi, ht12, ht23, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h8339, hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h5235, h8377, h8416, hc01, hc34, hlam, hphi, ht12, ht23, p8417_1]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [h8412, hlam, p8417_0]
                      · have p8417_0 := h8417c.1
                        have p8417_1 := h8417c.2.1
                        have p8417_2 := h8417c.2.2.1
                        have p8417_3 := h8417c.2.2.2
                        linarith only [hlam, p8417_0]
                    · linarith only [h6110, h8336, h8340, h8416, hlam]
                  · linarith only [h7104, h8336, h8415, hlam]
              · linarith only [h6110, h7104, h8336, h8338, h8412, hc01, hc12, hlam, hphi]
        · linarith only [h0, h7104, h8338, h8339, hc01, hc25, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8447 | h8447
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8448 | h8448
          · linarith only [h5235, h7979, h8337, h8338, h8448, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8450 | h8450
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8451 | h8451
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8452 | h8452
                · linarith only [h6110, h8337, h8338, h8448, h8452, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8454 | h8454
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8455 | h8455
                    · rcases h1bigk with h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c | h8456c
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h0, hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h5235, hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h6110, hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h6504, hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8338, h8452, hc01, hc34, hlam, hphi, ht12, ht23, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8338, h8452, hc13, hc34, hlam, hphi, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8338, hlam, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h6504, h8338, h8452, hc01, hc34, hlam, hphi, ht12, ht23, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8337, hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8448, hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h6504, h8337, h8338, h8452, hc01, hc34, hlam, hphi, ht12, ht23, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8338, h8452, hc12, hc34, hlam, hphi, ht23, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h5235, h8338, h8452, hc01, hc34, hlam, hphi, ht12, ht23, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h6504, h8338, h8452, hc01, hc34, hlam, hphi, ht12, ht23, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8337, h8450, hc01, hc12, hlam, hphi, p8456_1]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8447, hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8450, hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [h8451, hlam, p8456_0]
                      · have p8456_0 := h8456c.1
                        have p8456_1 := h8456c.2.1
                        have p8456_2 := h8456c.2.2.1
                        have p8456_3 := h8456c.2.2.2
                        linarith only [hlam, p8456_0]
                    · linarith only [h8336, h8338, h8447, h8452, h8455, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h6504, h8336, h8337, h8338, h8450, h8454, hlam]
              · linarith only [h6110, h6504, h8336, h8337, h8338, h8450, h8451, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8485 | h8485
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8486 | h8486
                · linarith only [h7979, h8336, h8337, h8338, h8486, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8488 | h8488
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8489 | h8489
                    · rcases h1bigk with h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h0, hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h5235, hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h6110, hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h6504, hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8338, h8486, hc01, hc34, hlam, hphi, ht12, ht23, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8338, h8486, hc13, hc34, hlam, hphi, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8338, hlam, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8338, h8486, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8337, hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8448, hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8450, hlam, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8338, h8486, hc12, hc34, hlam, hphi, ht23, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h5235, h8338, h8486, hc01, hc34, hlam, hphi, ht12, ht23, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h5235, h8338, h8450, h8486, hc01, hc34, hlam, hphi, ht12, ht23, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8447, hc01, hc12, hlam, hphi, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8447, hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h5235, h8338, h8447, h8486, hc01, hc34, hlam, hphi, ht12, ht23, p8490_1]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [h8485, hlam, p8490_0]
                      · have p8490_0 := h8490c.1
                        have p8490_1 := h8490c.2.1
                        have p8490_2 := h8490c.2.2.1
                        have p8490_3 := h8490c.2.2.2
                        linarith only [hlam, p8490_0]
                    · linarith only [h0, h8336, h8338, h8486, h8489, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h6504, h8336, h8338, h8447, h8488, hlam]
              · linarith only [h6110, h6504, h8336, h8338, h8447, h8485, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8519 | h8519
          · linarith only [h5235, h7979, h8337, h8338, h8519, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8521 | h8521
            · linarith only [h8337, h8447, h8521, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8523 | h8523
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8524 | h8524
                · linarith only [h6110, h8336, h8337, h8447, h8519, h8524, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8526 | h8526
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8527 | h8527
                    · rcases h1bigk with h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c | h8528c
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h0, hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h5235, hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h6110, hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h6504, hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h5235, hc01, hc12, hlam, hphi, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h8338, hlam, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h8447, hlam, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h8337, hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h8519, hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h8521, hlam, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h8338, h8524, hc01, hc34, hlam, hphi, ht12, ht23, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h8338, h8524, hc12, hc34, hlam, hphi, ht23, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h5235, h8338, h8524, hc01, hc34, hlam, hphi, ht12, ht23, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h6504, h8338, h8524, hc01, hc34, hlam, hphi, ht12, ht23, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h5235, h8337, h8447, h8524, h8526, hc01, hc34, hlam, hphi, ht12, ht23, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h5235, h8447, h8524, h8526, hc01, hc34, hlam, hphi, ht12, ht23, p8528_1]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [h8523, hlam, p8528_0]
                      · have p8528_0 := h8528c.1
                        have p8528_1 := h8528c.2.1
                        have p8528_2 := h8528c.2.2.1
                        have p8528_3 := h8528c.2.2.2
                        linarith only [hlam, p8528_0]
                    · linarith only [h6110, h8336, h8338, h8524, h8527, hlam]
                  · linarith only [h6110, h8336, h8338, h8526, hlam]
              · linarith only [h6110, h8336, h8523, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8557 | h8557
      · linarith only [h0, h7104, h8337, h8557, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8559 | h8559
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8560 | h8560
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8561 | h8561
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8562 | h8562
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8563 | h8563
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8564 | h8564
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8565 | h8565
                    · rcases h1bigk with h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c | h8566c
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h0, hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h5235, hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h6110, hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h6504, hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8557, h8563, hc01, hc23, hlam, hphi, ht12, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8337, hlam, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8557, hlam, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8557, h8563, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8337, hc01, hc23, hlam, hphi, ht12, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8337, hc12, hc23, hlam, hphi, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h6110, h8336, h8337, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h6504, h8337, hc01, hc23, hlam, hphi, ht12, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h6504, h8557, h8559, h8563, hc01, hc23, hlam, hphi, ht12, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8560, hlam, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h6504, h8557, h8563, hc01, hc23, hlam, hphi, ht12, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8559, hc01, hc12, hlam, hphi, p8566_1]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8559, hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8561, hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [h8562, hlam, p8566_0]
                      · have p8566_0 := h8566c.1
                        have p8566_1 := h8566c.2.1
                        have p8566_2 := h8566c.2.2.1
                        have p8566_3 := h8566c.2.2.2
                        linarith only [hlam, p8566_0]
                    · linarith only [h5235, h6110, h7979, h8336, h8557, h8563, h8565, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h6504, h7979, h8336, h8337, h8557, h8559, h8560, h8564, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h8337, h8560, h8563, hlam]
              · linarith only [h6110, h7979, h8336, h8337, h8560, h8562, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h5235, h7979, h8560, h8561, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8597 | h8597
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8598 | h8598
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8599 | h8599
                · linarith only [h6504, h8337, h8559, h8560, h8599, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h6504, h8337, h8559, h8599, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h6110, h8336, h8598, hlam]
            · linarith only [h8337, h8559, h8597, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8604 | h8604
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8605 | h8605
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8606 | h8606
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8607 | h8607
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8608 | h8608
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8609 | h8609
                    · rcases h1bigk with h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c | h8610c
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h0, hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h5235, hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h6110, hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h6504, hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h8337, hlam, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h8557, hlam, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h8559, hlam, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h8337, hc12, hc23, hlam, hphi, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h6110, h8337, hc01, hc23, hlam, hphi, ht12, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h6504, h8337, hc01, hc23, hlam, hphi, ht12, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h0, h8557, h8607, hc01, hc23, hlam, hphi, ht12, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h8604, hlam, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h0, h8557, h8559, h8607, hc01, hc23, hlam, hphi, ht12, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h0, h8559, hc01, hc25, hlam, hphi, ht12, p8610_1]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h8605, hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [h8606, hlam, p8610_0]
                      · have p8610_0 := h8610c.1
                        have p8610_1 := h8610c.2.1
                        have p8610_2 := h8610c.2.2.1
                        have p8610_3 := h8610c.2.2.2
                        linarith only [hlam, p8610_0]
                    · linarith only [h7979, h8336, h8609, hlam]
                  · linarith only [h6110, h7979, h8336, h8337, h8557, h8604, h8608, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h8337, h8604, h8607, hc01, hc14, hlam, hphi]
              · linarith only [h6110, h7979, h8336, h8337, h8604, h8606, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h5235, h7979, h8604, h8605, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8641 | h8641
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8642 | h8642
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8643 | h8643
                · linarith only [h0, h8559, h8604, h8641, h8643, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h8337, h8643, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h6110, h8336, h8642, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8647 | h8647
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8648 | h8648
                · linarith only [h0, h8337, h8604, h8648, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h8337, h8648, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h6110, h8336, h8647, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h8652 | h8652
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8653 | h8653
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8654 | h8654
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8655 | h8655
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8656 | h8656
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8657 | h8657
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8658 | h8658
                · linarith only [h5235, h7979, h8652, h8658, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8660 | h8660
                  · linarith only [h0, h7104, h8336, h8653, h8660, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h7104, h8657, h8660, hc01, hc14, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8663 | h8663
                · linarith only [h5235, h7979, h8652, h8663, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8665 | h8665
                  · linarith only [h8655, h8657, h8663, h8665, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8667 | h8667
                    · linarith only [h8655, h8657, h8667, hlam]
                    · rcases h1bigk with h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c | h8669c
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h0, hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h5235, hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h6110, hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h6504, hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [hc01, hc12, hlam, hphi, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h8656, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h0, h7104, h8655, h8663, hc01, hc12, hlam, hphi, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h6504, hc01, hc12, hlam, hphi, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h8652, hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h0, h7104, h8652, h8655, h8663, hc01, hc12, hlam, hphi, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h6504, h8652, hc01, hc12, hlam, hphi, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h8657, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h8653, hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h8655, hlam, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h8657, hlam, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h8654, hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h8656, hlam, p8669_0]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [h8657, hc14, hc45, hlam, hphi, p8669_1]
                      · have p8669_0 := h8669c.1
                        have p8669_1 := h8669c.2.1
                        have p8669_2 := h8669c.2.2.1
                        have p8669_3 := h8669c.2.2.2
                        linarith only [hlam, p8669_0]
            · linarith only [h5235, h7979, h8655, h8656, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8696 | h8696
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8697 | h8697
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8698 | h8698
                · linarith only [h5235, h8655, h8698, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8700 | h8700
                  · linarith only [h0, h7104, h8336, h8653, h8700, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h7104, h8697, h8700, hc01, hc14, hlam, hphi]
              · linarith only [h8655, h8696, h8697, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8704 | h8704
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8705 | h8705
                · linarith only [h5235, h7979, h8652, h8696, h8705, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8707 | h8707
                  · linarith only [h0, h7104, h8336, h8653, h8707, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h7104, h8704, h8707, hc01, hc14, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8710 | h8710
                · linarith only [h5235, h7979, h8652, h8655, h8704, h8710, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8712 | h8712
                  · linarith only [h5235, h8655, h8704, h8712, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8714 | h8714
                    · linarith only [h5235, h8655, h8704, h8714, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h5235, h8655, h8714, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
        · linarith only [h0, h7104, h8653, h8654, hc01, hc25, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8718 | h8718
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8719 | h8719
          · linarith only [h5235, h7979, h8652, h8653, h8719, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8721 | h8721
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8722 | h8722
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8723 | h8723
                · linarith only [h8652, h8653, h8719, h8723, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8725 | h8725
                  · linarith only [h0, h7104, h8336, h8653, h8718, h8723, h8725, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h8652, h8653, h8722, h8725, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h8652, h8653, h8721, h8722, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8729 | h8729
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8730 | h8730
                · linarith only [h6110, h8652, h8719, h8730, hc01, hc12, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8732 | h8732
                  · linarith only [h0, h7104, h8336, h8653, h8718, h8730, h8732, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h8652, h8653, h8729, h8732, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h8653, h8718, h8729, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8736 | h8736
          · linarith only [h5235, h7979, h8652, h8718, h8736, hc01, hc25, hlam, hphi, ht12]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8738 | h8738
            · linarith only [h8652, h8718, h8738, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8740 | h8740
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8741 | h8741
                · linarith only [h0, h7104, h8336, h8736, h8740, h8741, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8743 | h8743
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8744 | h8744
                    · rcases h1bigk with h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c | h8745c
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h0, hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h5235, hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h6110, hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h6504, hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h8718, h8741, h8743, hc01, hc34, hlam, hphi, ht12, ht23, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h8718, h8741, h8743, hc13, hc34, hlam, hphi, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h8653, hlam, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h8718, hlam, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [hc01, hc13, hlam, hphi, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h8652, hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h8736, hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h8738, hlam, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [hc01, hc14, hlam, hphi, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h8653, h8741, hc12, hc34, hlam, hphi, ht23, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h5235, h8653, h8741, hc01, hc34, hlam, hphi, ht12, ht23, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h5235, h8652, h8653, h8718, h8741, hc01, hc34, hlam, hphi, ht12, ht23, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [hc01, hc15, hlam, hphi, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h5235, h8652, h8718, h8741, h8743, hc01, hc34, hlam, hphi, ht12, ht23, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h5235, h8718, h8741, h8743, hc01, hc34, hlam, hphi, ht12, ht23, p8745_1]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [h8740, hlam, p8745_0]
                      · have p8745_0 := h8745c.1
                        have p8745_1 := h8745c.2.1
                        have p8745_2 := h8745c.2.2.1
                        have p8745_3 := h8745c.2.2.2
                        linarith only [hlam, p8745_0]
                    · linarith only [h5235, h8652, h8653, h8741, h8744, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h8653, h8740, h8743, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8773 | h8773
                · linarith only [h5235, h8736, h8773, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8775 | h8775
                  · linarith only [h6110, h8740, h8775, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h5235, h8652, h8653, h8775, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h8778 | h8778
      · linarith only [h0, h7104, h8652, h8778, hc01, hc23, hlam, hphi, ht12]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h8780 | h8780
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8781 | h8781
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8782 | h8782
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8783 | h8783
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8784 | h8784
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8785 | h8785
                  · linarith only [h0, h7104, h8336, h8778, h8780, h8784, h8785, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h8778, h8780, h8781, h8783, h8785, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h0, h7104, h8336, h8652, h8780, h8783, h8784, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h8778, h8780, h8783, hlam]
            · linarith only [h5235, h7979, h8781, h8782, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8791 | h8791
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8792 | h8792
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8793 | h8793
                · linarith only [h5235, h8781, h8793, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h8652, h8793, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h8778, h8780, h8792, hlam]
            · linarith only [h8652, h8780, h8791, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h8798 | h8798
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8799 | h8799
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8800 | h8800
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8801 | h8801
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8802 | h8802
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8803 | h8803
                    · linarith only [h0, h7104, h8336, h8798, h8803, hc01, hc13, hlam, hphi]
                    · linarith only [h5235, h7979, h8800, h8803, hc01, hc14, hlam, hphi]
                  · linarith only [h8778, h8800, h8802, hlam]
                · linarith only [h0, h7104, h8336, h8652, h8798, h8800, h8801, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8808 | h8808
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8809 | h8809
                  · linarith only [h5235, h7979, h8798, h8800, h8809, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h8778, h8809, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · linarith only [h0, h8652, h8798, h8808, hc01, hc13, hlam, hphi]
            · linarith only [h5235, h7979, h8798, h8799, hc01, hc35, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h8814 | h8814
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8815 | h8815
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8816 | h8816
                · linarith only [h5235, h8798, h8816, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h8652, h8816, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h8798, h8814, h8815, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h8820 | h8820
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8821 | h8821
                · linarith only [h5235, h8798, h8821, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h8652, h8821, hc01, hc34, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h8824 | h8824
                · linarith only [h0, h8652, h8798, h8824, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h8652, h8824, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h6504 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h7104 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5235 := hg5235
  rcases m.htr 0 3 4 (by decide) (by decide) with h7979 | h7979
  · exact r1l7_21_14_H_I_L_I_s6_x1_x1_x1_x0 m hb1 hb4 hg0 hg5235 h6110 h6504 h7104 h7979
  · exact r1l7_21_14_H_I_L_I_s6_x1_x1_x1_x1 m hb1 hb4 hg0 hg5235 h6110 h6504 h7104 h7979

set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x1_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h6504 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5235 := hg5235
  rcases m.htr 0 2 4 (by decide) (by decide) with h7104 | h7104
  · exact r1l7_21_14_H_I_L_I_s6_x1_x1_x0 m hb1 hb4 hg0 hg5235 h6110 h6504 h7104
  · exact r1l7_21_14_H_I_L_I_s6_x1_x1_x1 m hb1 hb4 hg0 hg5235 h6110 h6504 h7104

set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h6110 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5235 := hg5235
  rcases m.htr 0 1 5 (by decide) (by decide) with h6504 | h6504
  · exact r1l7_21_14_H_I_L_I_s6_x1_x0 m hb1 hb4 hg0 hg5235 h6110 h6504
  · exact r1l7_21_14_H_I_L_I_s6_x1_x1 m hb1 hb4 hg0 hg5235 h6110 h6504

set_option maxHeartbeats 5434000 in
set_option maxHeartbeats 5434000 in
theorem r1l7_21_14_H_I_L_I_s6 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5235 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5235 := hg5235
  rcases m.htr 0 1 4 (by decide) (by decide) with h6110 | h6110
  · exact r1l7_21_14_H_I_L_I_s6_x0 m hb1 hb4 hg0 hg5235 h6110
  · exact r1l7_21_14_H_I_L_I_s6_x1 m hb1 hb4 hg0 hg5235 h6110

end R2N4
