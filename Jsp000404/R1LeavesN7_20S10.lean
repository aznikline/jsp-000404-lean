import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_20S8
import Jsp000404.R1LeavesN7_20S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x1_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5036 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5037 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h5897 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 1 2 3 (by decide) (by decide) with h6293 | h6293
  · rcases m.htr 1 2 4 (by decide) (by decide) with h6294 | h6294
    · rcases m.htr 1 2 5 (by decide) (by decide) with h6295 | h6295
      · rcases m.htr 1 3 4 (by decide) (by decide) with h6296 | h6296
        · rcases m.htr 1 4 5 (by decide) (by decide) with h6297 | h6297
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6298 | h6298
            · linarith only [h5034, h5037, h6298, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6300 | h6300
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6301 | h6301
                · linarith only [h5035, h5897, h6301, hlam]
                · linarith only [h6298, h6300, h6301, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6304 | h6304
                · linarith only [h5035, h5897, h6304, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6306 | h6306
                  · linarith only [h3667, h5897, h6293, h6296, h6306, hc01, hc12, hlam, hphi]
                  · rcases h2bigk with h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c | h6308c
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h0, hlam, p6308_1]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      rcases p6308_3 (m.d 0 2) (by simp) with h6311 | h6311
                      · rcases p6308_3 (m.d 1 2) (by simp) with h6312 | h6312
                        · rcases p6308_3 (m.d 2 3) (by simp) with h6313 | h6313
                          · linarith only [h6313, hlam, p6308_0]
                          · rcases p6308_3 (m.d 2 4) (by simp) with h6315 | h6315
                            · linarith only [h5035, h6315, hlam]
                            · linarith only [h6298, h6315, hlam]
                        · linarith only [h6293, h6312, hlam]
                      · linarith only [h6311, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      rcases p6308_3 (m.d 0 2) (by simp) with h6320 | h6320
                      · rcases p6308_3 (m.d 1 2) (by simp) with h6321 | h6321
                        · rcases p6308_3 (m.d 2 3) (by simp) with h6322 | h6322
                          · linarith only [h5034, h6322, hlam]
                          · rcases p6308_3 (m.d 2 4) (by simp) with h6324 | h6324
                            · linarith only [h6324, hlam, p6308_0]
                            · rcases p6308_3 (m.d 2 5) (by simp) with h6326 | h6326
                              · linarith only [h5036, h6326, hlam]
                              · linarith only [h6304, h6326, hlam]
                        · linarith only [h6294, h6321, hlam]
                      · linarith only [h6320, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      rcases p6308_3 (m.d 0 2) (by simp) with h6331 | h6331
                      · rcases p6308_3 (m.d 1 2) (by simp) with h6332 | h6332
                        · rcases p6308_3 (m.d 2 3) (by simp) with h6333 | h6333
                          · linarith only [h5034, h6333, hlam]
                          · rcases p6308_3 (m.d 2 4) (by simp) with h6335 | h6335
                            · linarith only [h5035, h6335, hlam]
                            · rcases p6308_3 (m.d 2 5) (by simp) with h6337 | h6337
                              · linarith only [h6337, hlam, p6308_0]
                              · rcases h4bigk with h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c | h6339c
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h3667, hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h5037, h6293, h6296, h6297, h6298, h6306, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6339_1]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h5037, hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h5897, hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  rcases p6339_3 (m.d 0 4) (by simp) with h6345 | h6345
                                  · linarith only [h3667, h6345, hlam]
                                  · rcases p6339_3 (m.d 1 4) (by simp) with h6347 | h6347
                                    · rcases p6339_3 (m.d 2 4) (by simp) with h6348 | h6348
                                      · linarith only [h6294, h6348, hlam]
                                      · rcases p6339_3 (m.d 3 4) (by simp) with h6350 | h6350
                                        · linarith only [h6296, h6350, hlam]
                                        · linarith only [h5037, h6350, hlam]
                                    · linarith only [h3667, h6347, hlam]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  rcases p6339_3 (m.d 0 4) (by simp) with h6355 | h6355
                                  · linarith only [h3667, h6355, hlam]
                                  · linarith only [h5035, h6355, hlam]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  rcases p6339_3 (m.d 0 4) (by simp) with h6358 | h6358
                                  · linarith only [h3667, h6358, hlam]
                                  · rcases p6339_3 (m.d 1 4) (by simp) with h6360 | h6360
                                    · rcases p6339_3 (m.d 2 4) (by simp) with h6361 | h6361
                                      · linarith only [h6294, h6361, hlam]
                                      · rcases p6339_3 (m.d 3 4) (by simp) with h6363 | h6363
                                        · linarith only [h6296, h6363, hlam]
                                        · rcases p6339_3 (m.d 4 5) (by simp) with h6365 | h6365
                                          · linarith only [h6297, h6365, hlam]
                                          · linarith only [h6306, h6365, hlam]
                                    · linarith only [h6296, h6360, hlam]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h3667, h5037, h6306, hc01, hc14, hlam, hphi, p6339_1]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h5035, hlam, p6339_1]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h6294, hlam, p6339_1]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h6298, hlam, p6339_1]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h6304, hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h3667, h6306, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6339_1]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h6296, hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h6293, h6296, h6297, h6306, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6339_1]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h6306, hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h3667, h6293, h6296, h6297, hc01, hc12, hlam, hphi, p6339_1]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h6297, hlam, p6339_0]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  rcases p6339_3 (m.d 0 4) (by simp) with h6382 | h6382
                                  · linarith only [h5897, h6382, hlam]
                                  · linarith only [h5035, h6382, hlam]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [h5034, h5037, h6293, h6296, h6297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6339_1]
                                · have p6339_0 := h6339c.1
                                  have p6339_1 := h6339c.2.1
                                  have p6339_2 := h6339c.2.2.1
                                  have p6339_3 := h6339c.2.2.2
                                  linarith only [hlam, p6339_0]
                        · linarith only [h6295, h6332, hlam]
                      · linarith only [h6331, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p6308_1]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      rcases p6308_3 (m.d 0 2) (by simp) with h6391 | h6391
                      · linarith only [h0, h6391, hlam]
                      · linarith only [h5034, h6391, hlam]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      rcases p6308_3 (m.d 0 2) (by simp) with h6394 | h6394
                      · linarith only [h0, h6394, hlam]
                      · linarith only [h5035, h6394, hlam]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      rcases p6308_3 (m.d 0 2) (by simp) with h6397 | h6397
                      · linarith only [h0, h6397, hlam]
                      · linarith only [h5036, h6397, hlam]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h5034, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h6293, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h6298, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h6300, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h5035, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h6294, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h5036, h6304, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6308_1]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h6304, hlam, p6308_1]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h5036, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h6295, hlam, p6308_0]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h5036, h5897, h6293, h6296, h6297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6308_1]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [h5036, h5897, h6293, h6296, h6297, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6308_1]
                    · have p6308_0 := h6308c.1
                      have p6308_1 := h6308c.2.1
                      have p6308_2 := h6308c.2.2.1
                      have p6308_3 := h6308c.2.2.2
                      linarith only [hlam, p6308_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6415 | h6415
            · linarith only [h5034, h5037, h6415, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6417 | h6417
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6418 | h6418
                · linarith only [h5034, h5035, h5037, h6296, h6297, h6417, h6418, hc04, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h6415, h6417, h6418, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6421 | h6421
                · linarith only [h3667, h6297, h6421, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6423 | h6423
                  · linarith only [h3667, h6297, h6423, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h2bigk with h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h0, hlam, p6425_1]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      rcases p6425_3 (m.d 0 2) (by simp) with h6428 | h6428
                      · rcases p6425_3 (m.d 1 2) (by simp) with h6429 | h6429
                        · rcases p6425_3 (m.d 2 3) (by simp) with h6430 | h6430
                          · linarith only [h6430, hlam, p6425_0]
                          · rcases p6425_3 (m.d 2 4) (by simp) with h6432 | h6432
                            · linarith only [h5035, h6432, hlam]
                            · linarith only [h6415, h6432, hlam]
                        · linarith only [h6293, h6429, hlam]
                      · linarith only [h6428, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      rcases p6425_3 (m.d 0 2) (by simp) with h6437 | h6437
                      · rcases p6425_3 (m.d 1 2) (by simp) with h6438 | h6438
                        · rcases p6425_3 (m.d 2 3) (by simp) with h6439 | h6439
                          · linarith only [h5034, h6439, hlam]
                          · rcases p6425_3 (m.d 2 4) (by simp) with h6441 | h6441
                            · linarith only [h6441, hlam, p6425_0]
                            · rcases p6425_3 (m.d 2 5) (by simp) with h6443 | h6443
                              · linarith only [h5036, h6443, hlam]
                              · linarith only [h6421, h6443, hlam]
                        · linarith only [h6294, h6438, hlam]
                      · linarith only [h6437, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      rcases p6425_3 (m.d 0 2) (by simp) with h6448 | h6448
                      · rcases p6425_3 (m.d 1 2) (by simp) with h6449 | h6449
                        · rcases p6425_3 (m.d 2 3) (by simp) with h6450 | h6450
                          · linarith only [h5034, h6450, hlam]
                          · rcases p6425_3 (m.d 2 4) (by simp) with h6452 | h6452
                            · linarith only [h5035, h6452, hlam]
                            · rcases p6425_3 (m.d 2 5) (by simp) with h6454 | h6454
                              · linarith only [h6454, hlam, p6425_0]
                              · rcases h4bigk with h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c | h6456c
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h3667, hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h5037, h6296, h6297, h6415, hc23, hc45, hlam, hphi, ht34, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h5037, hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h5897, hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6297, hc04, hc45, hlam, hphi, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6297, h6415, hc23, hc45, hlam, hphi, ht34, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6297, hc34, hc45, hlam, hphi, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6297, hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h5035, hlam, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6294, hlam, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6415, hlam, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6421, hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h3667, h6293, h6296, hc01, hc12, hlam, hphi, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6296, hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6296, h6297, h6415, hc23, hc45, hlam, hphi, ht34, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h6423, hlam, p6456_0]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  rcases p6456_3 (m.d 0 4) (by simp) with h6477 | h6477
                                  · linarith only [h6477, hlam, p6456_0]
                                  · rcases p6456_3 (m.d 1 4) (by simp) with h6479 | h6479
                                    · linarith only [h6297, h6479, hlam]
                                    · linarith only [h3667, h6479, hlam]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h3667, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  rcases p6456_3 (m.d 0 4) (by simp) with h6483 | h6483
                                  · linarith only [h5897, h6483, hlam]
                                  · linarith only [h5035, h6483, hlam]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [h5034, h5037, hc23, hc45, hlam, hphi, ht34, p6456_1]
                                · have p6456_0 := h6456c.1
                                  have p6456_1 := h6456c.2.1
                                  have p6456_2 := h6456c.2.2.1
                                  have p6456_3 := h6456c.2.2.2
                                  linarith only [hlam, p6456_0]
                        · linarith only [h6295, h6449, hlam]
                      · linarith only [h6448, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p6425_1]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      rcases p6425_3 (m.d 0 2) (by simp) with h6492 | h6492
                      · linarith only [h0, h6492, hlam]
                      · linarith only [h5034, h6492, hlam]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      rcases p6425_3 (m.d 0 2) (by simp) with h6495 | h6495
                      · linarith only [h0, h6495, hlam]
                      · linarith only [h5035, h6495, hlam]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      rcases p6425_3 (m.d 0 2) (by simp) with h6498 | h6498
                      · linarith only [h0, h6498, hlam]
                      · linarith only [h5036, h6498, hlam]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h5034, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h6293, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h6415, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h6417, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h5035, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h6294, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h5036, h6421, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6425_1]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h6421, hlam, p6425_1]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h5036, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h6295, hlam, p6425_0]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h0, h5036, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6425_1]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [h0, h5036, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6425_1]
                    · have p6425_0 := h6425c.1
                      have p6425_1 := h6425c.2.1
                      have p6425_2 := h6425c.2.2.1
                      have p6425_3 := h6425c.2.2.2
                      linarith only [hlam, p6425_0]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h6516 | h6516
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6517 | h6517
            · linarith only [h3667, h5897, h6296, h6516, h6517, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6519 | h6519
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6520 | h6520
                · linarith only [h0, h3667, h5035, h5897, h6520, hc01, hc12, hlam, hphi]
                · linarith only [h6517, h6519, h6520, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6523 | h6523
                · linarith only [h0, h3667, h5035, h5897, h6523, hc01, hc12, hlam, hphi]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6525 | h6525
                  · rcases h2bigk with h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c | h6526c
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h0, hlam, p6526_1]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      rcases p6526_3 (m.d 0 2) (by simp) with h6529 | h6529
                      · rcases p6526_3 (m.d 1 2) (by simp) with h6530 | h6530
                        · rcases p6526_3 (m.d 2 3) (by simp) with h6531 | h6531
                          · linarith only [h6531, hlam, p6526_0]
                          · rcases p6526_3 (m.d 2 4) (by simp) with h6533 | h6533
                            · linarith only [h5035, h6533, hlam]
                            · linarith only [h6517, h6533, hlam]
                        · linarith only [h6293, h6530, hlam]
                      · linarith only [h6529, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      rcases p6526_3 (m.d 0 2) (by simp) with h6538 | h6538
                      · rcases p6526_3 (m.d 1 2) (by simp) with h6539 | h6539
                        · rcases p6526_3 (m.d 2 3) (by simp) with h6540 | h6540
                          · linarith only [h5034, h6540, hlam]
                          · rcases p6526_3 (m.d 2 4) (by simp) with h6542 | h6542
                            · linarith only [h6542, hlam, p6526_0]
                            · rcases p6526_3 (m.d 2 5) (by simp) with h6544 | h6544
                              · linarith only [h5036, h6544, hlam]
                              · linarith only [h6523, h6544, hlam]
                        · linarith only [h6294, h6539, hlam]
                      · linarith only [h6538, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      rcases p6526_3 (m.d 0 2) (by simp) with h6549 | h6549
                      · rcases p6526_3 (m.d 1 2) (by simp) with h6550 | h6550
                        · rcases p6526_3 (m.d 2 3) (by simp) with h6551 | h6551
                          · linarith only [h5034, h6551, hlam]
                          · rcases p6526_3 (m.d 2 4) (by simp) with h6553 | h6553
                            · linarith only [h5035, h6553, hlam]
                            · rcases p6526_3 (m.d 2 5) (by simp) with h6555 | h6555
                              · linarith only [h6555, hlam, p6526_0]
                              · rcases h4bigk with h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c | h6557c
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h3667, hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h5897, h6517, h6525, hc23, hc35, hlam, hphi, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h5037, hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h5897, hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  rcases p6557_3 (m.d 0 4) (by simp) with h6563 | h6563
                                  · linarith only [h3667, h6563, hlam]
                                  · rcases p6557_3 (m.d 1 4) (by simp) with h6565 | h6565
                                    · rcases p6557_3 (m.d 2 4) (by simp) with h6566 | h6566
                                      · linarith only [h6294, h6566, hlam]
                                      · rcases p6557_3 (m.d 3 4) (by simp) with h6568 | h6568
                                        · rcases p6557_3 (m.d 4 5) (by simp) with h6569 | h6569
                                          · linarith only [h6516, h6569, hlam]
                                          · linarith only [h5897, h6569, hlam]
                                        · linarith only [h5037, h6568, hlam]
                                    · linarith only [h3667, h6565, hlam]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  rcases p6557_3 (m.d 0 4) (by simp) with h6575 | h6575
                                  · linarith only [h3667, h6575, hlam]
                                  · linarith only [h5035, h6575, hlam]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h6296, hlam, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h5037, h5897, h6296, hc03, hc34, hlam, hphi, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h5035, hlam, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h6294, hlam, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h6517, hlam, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h6523, hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  rcases p6557_3 (m.d 0 4) (by simp) with h6585 | h6585
                                  · linarith only [h5037, h6585, hlam]
                                  · rcases p6557_3 (m.d 1 4) (by simp) with h6587 | h6587
                                    · linarith only [h6296, h6587, hlam]
                                    · linarith only [h3667, h6587, hlam]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h0, h3667, h6517, h6523, hc01, hc12, hc23, hc34, hlam, hphi, p6526_1, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  rcases p6557_3 (m.d 0 4) (by simp) with h6591 | h6591
                                  · linarith only [h5037, h6591, hlam]
                                  · linarith only [h5035, h6591, hlam]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h0, h3667, h5897, h6517, h6523, hc01, hc12, hc23, hc34, hlam, hphi, p6526_1, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h3667, h6516, hc01, hc14, hlam, hphi, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h6516, hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h6296, h6516, h6517, hc23, hc34, hlam, hphi, p6557_1]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [h6525, hlam, p6557_0]
                                · have p6557_0 := h6557c.1
                                  have p6557_1 := h6557c.2.1
                                  have p6557_2 := h6557c.2.2.1
                                  have p6557_3 := h6557c.2.2.2
                                  linarith only [hlam, p6557_0]
                        · linarith only [h6295, h6550, hlam]
                      · linarith only [h6549, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p6526_1]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      rcases p6526_3 (m.d 0 2) (by simp) with h6605 | h6605
                      · linarith only [h0, h6605, hlam]
                      · linarith only [h5034, h6605, hlam]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      rcases p6526_3 (m.d 0 2) (by simp) with h6608 | h6608
                      · linarith only [h0, h6608, hlam]
                      · linarith only [h5035, h6608, hlam]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      rcases p6526_3 (m.d 0 2) (by simp) with h6611 | h6611
                      · linarith only [h0, h6611, hlam]
                      · linarith only [h5036, h6611, hlam]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h5034, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h6293, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h6517, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h6519, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h5035, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h6294, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h5036, h6523, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6526_1]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h6523, hlam, p6526_1]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h5036, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h6295, hlam, p6526_0]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h5036, h5897, h6296, h6516, hc23, hc34, hlam, hphi, p6526_1]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [h5036, h5897, h6296, h6516, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p6526_1]
                    · have p6526_0 := h6526c.1
                      have p6526_1 := h6526c.2.1
                      have p6526_2 := h6526c.2.2.1
                      have p6526_3 := h6526c.2.2.2
                      linarith only [hlam, p6526_0]
                  · linarith only [h6296, h6516, h6525, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h6630 | h6630
            · linarith only [h5034, h5037, h6630, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h6632 | h6632
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6633 | h6633
                · linarith only [h3667, h6516, h6633, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h6630, h6632, h6633, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h6636 | h6636
                · linarith only [h3667, h6516, h6636, hc01, hc24, hlam, hphi, ht12]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h6638 | h6638
                  · linarith only [h3667, h6516, h6638, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases h2bigk with h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c | h6640c
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h0, hlam, p6640_1]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      rcases p6640_3 (m.d 0 2) (by simp) with h6643 | h6643
                      · rcases p6640_3 (m.d 1 2) (by simp) with h6644 | h6644
                        · rcases p6640_3 (m.d 2 3) (by simp) with h6645 | h6645
                          · linarith only [h6645, hlam, p6640_0]
                          · rcases p6640_3 (m.d 2 4) (by simp) with h6647 | h6647
                            · linarith only [h5035, h6647, hlam]
                            · linarith only [h6630, h6647, hlam]
                        · linarith only [h6293, h6644, hlam]
                      · linarith only [h6643, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      rcases p6640_3 (m.d 0 2) (by simp) with h6652 | h6652
                      · rcases p6640_3 (m.d 1 2) (by simp) with h6653 | h6653
                        · rcases p6640_3 (m.d 2 3) (by simp) with h6654 | h6654
                          · linarith only [h5034, h6654, hlam]
                          · rcases p6640_3 (m.d 2 4) (by simp) with h6656 | h6656
                            · linarith only [h6656, hlam, p6640_0]
                            · rcases p6640_3 (m.d 2 5) (by simp) with h6658 | h6658
                              · linarith only [h5036, h6658, hlam]
                              · linarith only [h6636, h6658, hlam]
                        · linarith only [h6294, h6653, hlam]
                      · linarith only [h6652, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      rcases p6640_3 (m.d 0 2) (by simp) with h6663 | h6663
                      · rcases p6640_3 (m.d 1 2) (by simp) with h6664 | h6664
                        · rcases p6640_3 (m.d 2 3) (by simp) with h6665 | h6665
                          · linarith only [h5034, h6665, hlam]
                          · rcases p6640_3 (m.d 2 4) (by simp) with h6667 | h6667
                            · linarith only [h5035, h6667, hlam]
                            · rcases p6640_3 (m.d 2 5) (by simp) with h6669 | h6669
                              · linarith only [h6669, hlam, p6640_0]
                              · rcases h4bigk with h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c | h6671c
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h3667, hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h3667, h6296, h6630, h6638, hc23, hc45, hlam, hphi, ht34, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h5037, hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h5897, hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6296, h6638, hc04, hc45, hlam, hphi, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6296, h6630, h6638, hc23, hc45, hlam, hphi, ht34, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6296, hlam, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6516, hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h5035, hlam, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6294, hlam, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6630, hlam, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6636, hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h3667, h6638, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6638, hc14, hc45, hlam, hphi, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6630, h6638, hc23, hc45, hlam, hphi, ht34, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6638, hlam, p6671_0]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  rcases p6671_3 (m.d 0 4) (by simp) with h6692 | h6692
                                  · linarith only [h6692, hlam, p6671_0]
                                  · rcases p6671_3 (m.d 1 4) (by simp) with h6694 | h6694
                                    · linarith only [h6516, h6694, hlam]
                                    · linarith only [h3667, h6694, hlam]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h0, h3667, h6630, h6636, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p6640_1, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  rcases p6671_3 (m.d 0 4) (by simp) with h6698 | h6698
                                  · linarith only [h5897, h6698, hlam]
                                  · linarith only [h5035, h6698, hlam]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [h6296, hc13, hc45, hlam, hphi, ht34, p6671_1]
                                · have p6671_0 := h6671c.1
                                  have p6671_1 := h6671c.2.1
                                  have p6671_2 := h6671c.2.2.1
                                  have p6671_3 := h6671c.2.2.2
                                  linarith only [hlam, p6671_0]
                        · linarith only [h6295, h6664, hlam]
                      · linarith only [h6663, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h0, hc01, hc12, hlam, hphi, p6640_1]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      rcases p6640_3 (m.d 0 2) (by simp) with h6707 | h6707
                      · linarith only [h0, h6707, hlam]
                      · linarith only [h5034, h6707, hlam]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      rcases p6640_3 (m.d 0 2) (by simp) with h6710 | h6710
                      · linarith only [h0, h6710, hlam]
                      · linarith only [h5035, h6710, hlam]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      rcases p6640_3 (m.d 0 2) (by simp) with h6713 | h6713
                      · linarith only [h0, h6713, hlam]
                      · linarith only [h5036, h6713, hlam]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h5034, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h6293, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h6630, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h6632, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h5035, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h6294, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h5036, h6636, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6640_1]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h6636, hlam, p6640_1]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h5036, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h6295, hlam, p6640_0]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h0, h5036, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6640_1]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [h0, h5036, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6640_1]
                    · have p6640_0 := h6640c.1
                      have p6640_1 := h6640c.2.1
                      have p6640_2 := h6640c.2.2.1
                      have p6640_3 := h6640c.2.2.2
                      linarith only [hlam, p6640_0]
      · linarith only [h0, h5036, h6295, hlam]
    · linarith only [h0, h5035, h6294, hlam]
  · linarith only [h0, h5034, h6293, hlam]

set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5036 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5037 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 4 5 (by decide) (by decide) with h5897 | h5897
  · exact r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x1_x0 m hb2 hb4 hg0 hg3667 h5034 h5035 h5036 h5037 h5897
  · exact r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x1_x1 m hb2 hb4 hg0 hg3667 h5034 h5035 h5036 h5037 h5897

set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5036 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 3 4 (by decide) (by decide) with h5037 | h5037
  · exact r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x0 m hb2 hb4 hg0 hg3667 h5034 h5035 h5036 h5037
  · exact r1l7_22_14_H_I_L_I_s3_x0_x0_x0_x1 m hb2 hb4 hg0 hg3667 h5034 h5035 h5036 h5037

set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h5036 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 3 4 (by decide) (by decide) with h6734 | h6734
  · rcases m.htr 0 4 5 (by decide) (by decide) with h6735 | h6735
    · linarith only [h5035, h5036, h6735, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6737 | h6737
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6738 | h6738
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6739 | h6739
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6740 | h6740
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6741 | h6741
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6742 | h6742
                · linarith only [h5034, h5036, h6739, h6742, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h5034, h5036, h6734, h6739, h6742, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6745 | h6745
                · linarith only [h5034, h5036, h6739, h6745, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h5034, h5036, h6734, h6739, h6745, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h5034, h5036, h6734, h6739, h6740, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6749 | h6749
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6750 | h6750
              · linarith only [h3667, h6735, h6737, h6739, h6749, h6750, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6752 | h6752
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6753 | h6753
                  · linarith only [h0, h5034, h6739, h6753, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6755 | h6755
                    · linarith only [h5035, h6735, h6755, hlam]
                    · linarith only [h0, h5034, h6739, h6752, h6755, hc34, hc45, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6758 | h6758
                  · linarith only [h0, h5034, h6734, h6739, h6752, h6758, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h5034, h6734, h6739, h6752, h6758, hc23, hc35, hlam, hphi]
            · linarith only [h0, h3667, h5034, h6734, h6739, h6749, hc01, hc25, hlam, hphi, ht12]
        · linarith only [h0, h5035, h6738, hlam]
      · linarith only [h0, h5034, h6737, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h6764 | h6764
    · linarith only [h5035, h5036, h6764, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h6766 | h6766
      · rcases m.htr 1 2 4 (by decide) (by decide) with h6767 | h6767
        · rcases m.htr 1 2 5 (by decide) (by decide) with h6768 | h6768
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6769 | h6769
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6770 | h6770
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6771 | h6771
                · linarith only [h5034, h5036, h6734, h6768, h6771, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6773 | h6773
                  · linarith only [h5034, h5036, h6768, h6773, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6775 | h6775
                    · linarith only [h5035, h5036, h6764, h6768, h6775, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6777 | h6777
                      · linarith only [h5035, h5036, h6771, h6775, h6777, hc23, hc34, hlam, hphi]
                      · rcases h2bigk with h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c | h6779c
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h0, hlam, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h5036, h6766, h6769, h6770, h6773, h6777, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h5036, h6766, h6769, h6770, h6773, h6777, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h5036, hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          rcases p6779_3 (m.d 0 2) (by simp) with h6787 | h6787
                          · linarith only [h0, h6787, hlam]
                          · linarith only [h5034, h6787, hlam]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          rcases p6779_3 (m.d 0 2) (by simp) with h6790 | h6790
                          · linarith only [h0, h6790, hlam]
                          · linarith only [h5035, h6790, hlam]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h5035, h5036, h6771, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h5034, hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h6766, hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h6771, hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h6773, hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h5035, hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h6767, hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h6775, hlam, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [hc02, hc25, hlam, hphi, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h6768, hlam, p6779_0]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h6766, h6769, h6770, h6773, h6777, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [h6766, h6769, h6770, h6771, h6773, h6777, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6779_1]
                        · have p6779_0 := h6779c.1
                          have p6779_1 := h6779c.2.1
                          have p6779_2 := h6779c.2.2.1
                          have p6779_3 := h6779c.2.2.2
                          linarith only [hlam, p6779_0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6809 | h6809
                · linarith only [h5034, h6734, h6809, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6811 | h6811
                  · linarith only [h5035, h5036, h6768, h6809, h6811, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6813 | h6813
                    · linarith only [h5035, h5036, h6768, h6770, h6813, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6815 | h6815
                      · linarith only [h5035, h5036, h6768, h6770, h6809, h6815, hc23, hc34, hlam, hphi]
                      · rcases h2bigk with h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c | h6817c
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h0, hlam, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h5036, h6768, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h5036, h6768, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h5036, hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          rcases p6817_3 (m.d 0 2) (by simp) with h6825 | h6825
                          · linarith only [h0, h6825, hlam]
                          · linarith only [h5034, h6825, hlam]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          rcases p6817_3 (m.d 0 2) (by simp) with h6828 | h6828
                          · linarith only [h0, h6828, hlam]
                          · linarith only [h5035, h6828, hlam]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h5035, h5036, h6809, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h5034, hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h6766, hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h6809, hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h6811, hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h5035, hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h6767, hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h6813, hlam, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [hc02, hc25, hlam, hphi, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h6768, hlam, p6817_0]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h6768, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [h6768, h6809, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6817_1]
                        · have p6817_0 := h6817c.1
                          have p6817_1 := h6817c.2.1
                          have p6817_2 := h6817c.2.2.1
                          have p6817_3 := h6817c.2.2.2
                          linarith only [hlam, p6817_0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6847 | h6847
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6848 | h6848
                · linarith only [h3667, h6764, h6769, h6847, h6848, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6850 | h6850
                  · linarith only [h5035, h5036, h6768, h6848, h6850, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6852 | h6852
                    · linarith only [h3667, h5035, h5036, h6764, h6768, h6852, hc01, hc12, hlam, hphi]
                    · linarith only [h5035, h5036, h6769, h6847, h6848, h6852, hc23, hc34, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6855 | h6855
                · linarith only [h5034, h5036, h6768, h6855, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6857 | h6857
                  · linarith only [h5034, h5036, h6768, h6857, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6859 | h6859
                    · linarith only [h5035, h5036, h6768, h6859, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6861 | h6861
                      · linarith only [h5035, h5036, h6768, h6847, h6855, h6861, hc23, hc34, hlam, hphi]
                      · rcases h2bigk with h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c | h6863c
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h0, hlam, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h5036, h6768, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h5036, h6768, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h5036, hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          rcases p6863_3 (m.d 0 2) (by simp) with h6871 | h6871
                          · linarith only [h0, h6871, hlam]
                          · linarith only [h5034, h6871, hlam]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          rcases p6863_3 (m.d 0 2) (by simp) with h6874 | h6874
                          · linarith only [h0, h6874, hlam]
                          · linarith only [h5035, h6874, hlam]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h5035, h5036, h6855, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h5034, hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h6766, hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h6855, hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h6857, hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h5035, hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h6767, hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h6859, hlam, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [hc02, hc25, hlam, hphi, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h6768, hlam, p6863_0]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h6768, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [h6768, h6855, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6863_1]
                        · have p6863_0 := h6863c.1
                          have p6863_1 := h6863c.2.1
                          have p6863_2 := h6863c.2.2.1
                          have p6863_3 := h6863c.2.2.2
                          linarith only [hlam, p6863_0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h6893 | h6893
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6894 | h6894
              · linarith only [h3667, h6764, h6767, h6768, h6894, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6896 | h6896
                · linarith only [h5034, h6734, h6896, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6898 | h6898
                  · linarith only [h5034, h6734, h6766, h6768, h6893, h6898, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h6734, h6766, h6768, h6893, h6898, hc03, hc35, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6901 | h6901
              · linarith only [h3667, h6764, h6767, h6768, h6901, hc01, hc25, hlam, hphi, ht12]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6903 | h6903
                · linarith only [h0, h3667, h5034, h6768, h6893, h6903, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6905 | h6905
                  · linarith only [h0, h5035, h6768, h6903, h6905, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6907 | h6907
                    · linarith only [h0, h3667, h5035, h6768, h6901, h6905, h6907, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6909 | h6909
                      · linarith only [h0, h5035, h6768, h6903, h6907, h6909, hc23, hc34, hlam, hphi]
                      · rcases h2bigk with h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c | h6911c
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h0, hlam, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h0, h6768, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h0, h6768, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h5036, hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6768, hc02, hc25, hlam, hphi, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6768, h6905, h6909, hc23, hc45, hlam, hphi, ht34, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6768, h6905, h6909, hc24, hc45, hlam, hphi, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6768, hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h5034, hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6766, hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6903, hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6905, hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h5035, hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6767, hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h5035, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [hlam, p6911_0]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6907, hlam, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6905, h6909, hc02, hc45, hlam, hphi, ht23, ht34, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h3667, h6767, h6905, h6909, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6905, h6909, hc23, hc45, hlam, hphi, ht34, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [h6903, h6905, h6909, hc23, hc45, hlam, hphi, ht34, p6911_1]
                        · have p6911_0 := h6911c.1
                          have p6911_1 := h6911c.2.1
                          have p6911_2 := h6911c.2.2.1
                          have p6911_3 := h6911c.2.2.2
                          linarith only [hlam, p6911_0]
        · linarith only [h0, h5035, h6767, hlam]
      · linarith only [h0, h5034, h6766, hlam]

set_option maxHeartbeats 6518000 in
set_option maxHeartbeats 6518000 in
theorem r1l7_22_14_H_I_L_I_s3_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3667 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h5034 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5035 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h4bigk := hb4.1
  have h0 := hg0
  have h3667 := hg3667
  rcases m.htr 0 2 5 (by decide) (by decide) with h5036 | h5036
  · exact r1l7_22_14_H_I_L_I_s3_x0_x0_x0 m hb2 hb4 hg0 hg3667 h5034 h5035 h5036
  · exact r1l7_22_14_H_I_L_I_s3_x0_x0_x1 m hb2 hb4 hg0 hg3667 h5034 h5035 h5036

end R2N4
