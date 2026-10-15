import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S55
import Jsp000404.R1LeavesN7_0S59

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h19745 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 3 4 (by decide) (by decide) with h21279 | h21279
  · rcases m.htr 0 3 5 (by decide) (by decide) with h21280 | h21280
    · rcases m.htr 0 4 5 (by decide) (by decide) with h21281 | h21281
      · linarith only [h19744, h19745, h21281, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h21283 | h21283
        · linarith only [h0, h21283, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h21285 | h21285
          · rcases m.htr 1 2 5 (by decide) (by decide) with h21286 | h21286
            · linarith only [h0, h19745, h21286, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h21288 | h21288
              · rcases m.htr 1 3 5 (by decide) (by decide) with h21289 | h21289
                · rcases m.htr 1 4 5 (by decide) (by decide) with h21290 | h21290
                  · linarith only [h2, h21281, h21290, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h21292 | h21292
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h21293 | h21293
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h21294 | h21294
                        · linarith only [h0, h19745, h2, h21281, h21285, h21293, h21294, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h21296 | h21296
                          · linarith only [h19744, h19745, h21292, h21294, h21296, hlam]
                          · rcases h1bigk with h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c | h21298c
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              rcases p21298_3 (m.d 0 1) (by simp) with h21300 | h21300
                              · rcases p21298_3 (m.d 1 2) (by simp) with h21301 | h21301
                                · linarith only [h21301, hlam, p21298_0]
                                · rcases p21298_3 (m.d 1 3) (by simp) with h21303 | h21303
                                  · linarith only [h1, h21303, hlam]
                                  · linarith only [h21283, h21303, hlam]
                              · linarith only [h21300, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              rcases p21298_3 (m.d 0 1) (by simp) with h21307 | h21307
                              · rcases p21298_3 (m.d 1 2) (by simp) with h21308 | h21308
                                · linarith only [h0, h21308, hlam]
                                · rcases p21298_3 (m.d 1 3) (by simp) with h21310 | h21310
                                  · linarith only [h21310, hlam, p21298_0]
                                  · rcases p21298_3 (m.d 1 4) (by simp) with h21312 | h21312
                                    · linarith only [h2, h21312, hlam]
                                    · rcases p21298_3 (m.d 1 5) (by simp) with h21314 | h21314
                                      · linarith only [h21314, h3, hlam]
                                      · rcases h1emax with h21316 | h21316 | h21316 | h21316 | h21316
                                        · linarith only [h0, h21285, h21292, h21316, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                        · rcases h2bigk with h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c | h21318c
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h19745, h21285, h21292, h21293, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21318_1]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h4, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h19745, h21292, h21294, hc34, hc45, hlam, hphi, p21318_1]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h19745, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h0, hlam, p21318_1]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h21283, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h21286, h21289, h21292, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21298_1, p21318_1]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h21286, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            rcases p21318_3 (m.d 0 2) (by simp) with h21329 | h21329
                                            · linarith only [h21329, hlam, p21318_0]
                                            · rcases p21318_3 (m.d 1 2) (by simp) with h21331 | h21331
                                              · linarith only [h21283, h21331, hlam]
                                              · rcases p21318_3 (m.d 2 3) (by simp) with h21333 | h21333
                                                · rcases p21318_3 (m.d 2 4) (by simp) with h21334 | h21334
                                                  · linarith only [h21292, h21334, hlam]
                                                  · rcases p21318_3 (m.d 2 5) (by simp) with h21336 | h21336
                                                    · linarith only [h21293, h21336, hlam]
                                                    · linarith only [h19745, h21336, hlam]
                                                · linarith only [h21333, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            rcases p21318_3 (m.d 0 2) (by simp) with h21340 | h21340
                                            · linarith only [h21340, h4, hlam]
                                            · linarith only [h0, h21340, hlam]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            rcases p21318_3 (m.d 0 2) (by simp) with h21344 | h21344
                                            · linarith only [h21344, h4, hlam]
                                            · linarith only [h19744, h21344, hlam]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21318_1]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h19744, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h21285, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h21292, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h21294, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h0, h21285, h21292, h21294, hc34, hc45, hlam, hphi, p21318_1]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h21285, h21292, h21294, hc34, hc45, hlam, hphi, p21318_1]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [h21293, hlam, p21318_0]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            rcases p21318_3 (m.d 0 2) (by simp) with h21356 | h21356
                                            · linarith only [h19745, h21356, hlam]
                                            · linarith only [h19744, h21356, hlam]
                                          · have p21318_0 := h21318c.1
                                            have p21318_1 := h21318c.2.1
                                            have p21318_2 := h21318c.2.2.1
                                            have p21318_3 := h21318c.2.2.2
                                            linarith only [hlam, p21318_0]
                                        · rcases h2bigk with h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c | h21360c
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h21285, h21292, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21360_1]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h4, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h19745, h21292, h21294, hc34, hc45, hlam, hphi, p21360_1]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h19745, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h0, hlam, p21360_1]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h21283, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h0, h19745, h21292, h21294, hc34, hc45, hlam, hphi, p21360_1]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h21286, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            rcases p21360_3 (m.d 0 2) (by simp) with h21371 | h21371
                                            · linarith only [h21371, hlam, p21360_0]
                                            · rcases p21360_3 (m.d 1 2) (by simp) with h21373 | h21373
                                              · linarith only [h21283, h21373, hlam]
                                              · rcases p21360_3 (m.d 2 3) (by simp) with h21375 | h21375
                                                · rcases p21360_3 (m.d 2 4) (by simp) with h21376 | h21376
                                                  · linarith only [h21292, h21376, hlam]
                                                  · rcases p21360_3 (m.d 2 5) (by simp) with h21378 | h21378
                                                    · linarith only [h21293, h21378, hlam]
                                                    · linarith only [h19745, h21378, hlam]
                                                · linarith only [h21375, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            rcases p21360_3 (m.d 0 2) (by simp) with h21382 | h21382
                                            · linarith only [h21382, h4, hlam]
                                            · linarith only [h0, h21382, hlam]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            rcases p21360_3 (m.d 0 2) (by simp) with h21386 | h21386
                                            · linarith only [h21386, h4, hlam]
                                            · linarith only [h19744, h21386, hlam]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21360_1]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h19744, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h21285, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h21292, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h21294, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h0, h21285, h21292, h21294, hc34, hc45, hlam, hphi, p21360_1]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h21285, h21292, h21294, hc34, hc45, hlam, hphi, p21360_1]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [h21293, hlam, p21360_0]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            rcases p21360_3 (m.d 0 2) (by simp) with h21398 | h21398
                                            · linarith only [h19745, h21398, hlam]
                                            · linarith only [h19744, h21398, hlam]
                                          · have p21360_0 := h21360c.1
                                            have p21360_1 := h21360c.2.1
                                            have p21360_2 := h21360c.2.2.1
                                            have p21360_3 := h21360c.2.2.2
                                            linarith only [hlam, p21360_0]
                                        · rcases h2bigk with h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c | h21402c
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h21285, h21292, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21402_1]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h4, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h19745, h21292, h21294, hc34, hc45, hlam, hphi, p21402_1]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h19745, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h0, hlam, p21402_1]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h21283, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h0, h19745, h21292, h21294, hc34, hc45, hlam, hphi, p21402_1]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h21286, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            rcases p21402_3 (m.d 0 2) (by simp) with h21413 | h21413
                                            · linarith only [h21413, hlam, p21402_0]
                                            · rcases p21402_3 (m.d 1 2) (by simp) with h21415 | h21415
                                              · linarith only [h21283, h21415, hlam]
                                              · rcases p21402_3 (m.d 2 3) (by simp) with h21417 | h21417
                                                · rcases p21402_3 (m.d 2 4) (by simp) with h21418 | h21418
                                                  · linarith only [h21292, h21418, hlam]
                                                  · rcases p21402_3 (m.d 2 5) (by simp) with h21420 | h21420
                                                    · linarith only [h21293, h21420, hlam]
                                                    · linarith only [h19745, h21420, hlam]
                                                · linarith only [h21417, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            rcases p21402_3 (m.d 0 2) (by simp) with h21424 | h21424
                                            · linarith only [h21424, h4, hlam]
                                            · linarith only [h0, h21424, hlam]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            rcases p21402_3 (m.d 0 2) (by simp) with h21428 | h21428
                                            · linarith only [h21428, h4, hlam]
                                            · linarith only [h19744, h21428, hlam]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21402_1]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h19744, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h21285, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h21292, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h21294, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h0, h21285, h21292, h21294, hc34, hc45, hlam, hphi, p21402_1]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h21285, h21292, h21294, hc34, hc45, hlam, hphi, p21402_1]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [h21293, hlam, p21402_0]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            rcases p21402_3 (m.d 0 2) (by simp) with h21440 | h21440
                                            · linarith only [h19745, h21440, hlam]
                                            · linarith only [h19744, h21440, hlam]
                                          · have p21402_0 := h21402c.1
                                            have p21402_1 := h21402c.2.1
                                            have p21402_2 := h21402c.2.2.1
                                            have p21402_3 := h21402c.2.2.2
                                            linarith only [hlam, p21402_0]
                                        · rcases h2bigk with h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c | h21444c
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h21285, h21292, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21444_1]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h4, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h19745, h21292, h21294, hc34, hc45, hlam, hphi, p21444_1]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h19745, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h0, hlam, p21444_1]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h21283, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h0, h19745, h21292, h21294, hc34, hc45, hlam, hphi, p21444_1]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h21286, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            rcases p21444_3 (m.d 0 2) (by simp) with h21455 | h21455
                                            · linarith only [h21455, hlam, p21444_0]
                                            · rcases p21444_3 (m.d 1 2) (by simp) with h21457 | h21457
                                              · linarith only [h21283, h21457, hlam]
                                              · rcases p21444_3 (m.d 2 3) (by simp) with h21459 | h21459
                                                · rcases p21444_3 (m.d 2 4) (by simp) with h21460 | h21460
                                                  · linarith only [h21292, h21460, hlam]
                                                  · rcases p21444_3 (m.d 2 5) (by simp) with h21462 | h21462
                                                    · linarith only [h21293, h21462, hlam]
                                                    · linarith only [h19745, h21462, hlam]
                                                · linarith only [h21459, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            rcases p21444_3 (m.d 0 2) (by simp) with h21466 | h21466
                                            · linarith only [h21466, h4, hlam]
                                            · linarith only [h0, h21466, hlam]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            rcases p21444_3 (m.d 0 2) (by simp) with h21470 | h21470
                                            · linarith only [h21470, h4, hlam]
                                            · linarith only [h19744, h21470, hlam]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21444_1]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h19744, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h21285, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h21292, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h21294, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h0, h21285, h21292, h21294, hc34, hc45, hlam, hphi, p21444_1]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h21285, h21292, h21294, hc34, hc45, hlam, hphi, p21444_1]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [h21293, hlam, p21444_0]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            rcases p21444_3 (m.d 0 2) (by simp) with h21482 | h21482
                                            · linarith only [h19745, h21482, hlam]
                                            · linarith only [h19744, h21482, hlam]
                                          · have p21444_0 := h21444c.1
                                            have p21444_1 := h21444c.2.1
                                            have p21444_2 := h21444c.2.2.1
                                            have p21444_3 := h21444c.2.2.2
                                            linarith only [hlam, p21444_0]
                              · linarith only [h21307, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              rcases p21298_3 (m.d 0 1) (by simp) with h21487 | h21487
                              · rcases p21298_3 (m.d 1 2) (by simp) with h21488 | h21488
                                · linarith only [h0, h21488, hlam]
                                · linarith only [h21285, h21488, hlam]
                              · linarith only [h21487, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              rcases p21298_3 (m.d 0 1) (by simp) with h21492 | h21492
                              · rcases p21298_3 (m.d 1 2) (by simp) with h21493 | h21493
                                · linarith only [h0, h21493, hlam]
                                · rcases p21298_3 (m.d 1 3) (by simp) with h21495 | h21495
                                  · linarith only [h1, h21495, hlam]
                                  · linarith only [h21289, h21495, hlam]
                              · linarith only [h21492, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h0, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h21283, hlam, p21298_1]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h0, h19745, h21294, hc14, hc45, hlam, hphi, p21298_1]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h21286, hlam, p21298_1]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h1, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h1, h21285, h21292, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21298_1]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              rcases p21298_3 (m.d 0 1) (by simp) with h21507 | h21507
                              · rcases p21298_3 (m.d 1 2) (by simp) with h21508 | h21508
                                · linarith only [h21283, h21508, hlam]
                                · linarith only [h21285, h21508, hlam]
                              · linarith only [h2, h21507, hlam]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h1, h21285, h21286, h21292, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21298_1]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h2, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h21285, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h21288, hlam, p21298_1]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h21290, hlam, p21298_1]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h3, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h21285, h21292, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21298_1]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [h21289, hlam, p21298_0]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              rcases p21298_3 (m.d 0 1) (by simp) with h21521 | h21521
                              · rcases p21298_3 (m.d 1 2) (by simp) with h21522 | h21522
                                · linarith only [h21286, h21522, hlam]
                                · linarith only [h21285, h21522, hlam]
                              · linarith only [h2, h21521, hlam]
                            · have p21298_0 := h21298c.1
                              have p21298_1 := h21298c.2.1
                              have p21298_2 := h21298c.2.2.1
                              have p21298_3 := h21298c.2.2.2
                              linarith only [hlam, p21298_0]
                      · linarith only [h21280, h21293, h4, hlam]
                    · linarith only [h21279, h21292, h4, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h21529 | h21529
                  · linarith only [h2, h21281, h21529, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h21531 | h21531
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h21532 | h21532
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h21533 | h21533
                        · linarith only [h21280, h21281, h21283, h21285, h21289, h21533, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h21535 | h21535
                          · linarith only [h19745, h21280, h21283, h21285, h21289, h21531, h21533, h21535, hc02, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases h1bigk with h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c | h21537c
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              rcases p21537_3 (m.d 0 1) (by simp) with h21539 | h21539
                              · rcases p21537_3 (m.d 1 2) (by simp) with h21540 | h21540
                                · linarith only [h21540, hlam, p21537_0]
                                · rcases p21537_3 (m.d 1 3) (by simp) with h21542 | h21542
                                  · linarith only [h1, h21542, hlam]
                                  · linarith only [h21283, h21542, hlam]
                              · linarith only [h21539, hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              rcases p21537_3 (m.d 0 1) (by simp) with h21546 | h21546
                              · rcases p21537_3 (m.d 1 2) (by simp) with h21547 | h21547
                                · linarith only [h0, h21547, hlam]
                                · rcases p21537_3 (m.d 1 3) (by simp) with h21549 | h21549
                                  · linarith only [h21549, hlam, p21537_0]
                                  · rcases p21537_3 (m.d 1 4) (by simp) with h21551 | h21551
                                    · linarith only [h2, h21551, hlam]
                                    · rcases p21537_3 (m.d 1 5) (by simp) with h21553 | h21553
                                      · linarith only [h21553, h3, hlam]
                                      · linarith only [h21289, h21553, hlam]
                              · linarith only [h21546, hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              rcases p21537_3 (m.d 0 1) (by simp) with h21557 | h21557
                              · rcases p21537_3 (m.d 1 2) (by simp) with h21558 | h21558
                                · linarith only [h0, h21558, hlam]
                                · linarith only [h21285, h21558, hlam]
                              · linarith only [h21557, hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              rcases p21537_3 (m.d 0 1) (by simp) with h21562 | h21562
                              · rcases p21537_3 (m.d 1 2) (by simp) with h21563 | h21563
                                · linarith only [h0, h21563, hlam]
                                · rcases p21537_3 (m.d 1 3) (by simp) with h21565 | h21565
                                  · linarith only [h1, h21565, hlam]
                                  · rcases p21537_3 (m.d 1 4) (by simp) with h21567 | h21567
                                    · linarith only [h2, h21567, hlam]
                                    · rcases p21537_3 (m.d 1 5) (by simp) with h21569 | h21569
                                      · linarith only [h21569, hlam, p21537_0]
                                      · rcases h1emax with h21571 | h21571 | h21571 | h21571 | h21571
                                        · linarith only [h21571, hc15, hlam, hphi, ht01, ht0b, ht5b, p21537_1]
                                        · rcases h2bigk with h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c | h21573c
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h21285, h21531, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21573_1]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h4, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h19745, h21531, h21533, hc34, hc45, hlam, hphi, p21573_1]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h19745, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h0, hlam, p21573_1]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h21283, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h1, h21280, h21283, h21289, h21531, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21573_1]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h21286, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            rcases p21573_3 (m.d 0 2) (by simp) with h21584 | h21584
                                            · linarith only [h21584, hlam, p21573_0]
                                            · rcases p21573_3 (m.d 1 2) (by simp) with h21586 | h21586
                                              · linarith only [h21283, h21586, hlam]
                                              · rcases p21573_3 (m.d 2 3) (by simp) with h21588 | h21588
                                                · rcases p21573_3 (m.d 2 4) (by simp) with h21589 | h21589
                                                  · linarith only [h21531, h21589, hlam]
                                                  · rcases p21573_3 (m.d 2 5) (by simp) with h21591 | h21591
                                                    · linarith only [h21532, h21591, hlam]
                                                    · linarith only [h19745, h21591, hlam]
                                                · linarith only [h21588, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            rcases p21573_3 (m.d 0 2) (by simp) with h21595 | h21595
                                            · linarith only [h21595, h4, hlam]
                                            · linarith only [h0, h21595, hlam]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h21280, h21283, h21285, h21289, h4, hlam, p21573_2]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21573_1]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h19744, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h21285, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h21531, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h21533, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h0, h21285, h21531, h21533, hc34, hc45, hlam, hphi, p21573_1]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h21285, h21531, h21533, hc34, hc45, hlam, hphi, p21573_1]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [h21532, hlam, p21573_0]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            rcases p21573_3 (m.d 0 2) (by simp) with h21609 | h21609
                                            · linarith only [h19745, h21609, hlam]
                                            · linarith only [h19744, h21609, hlam]
                                          · have p21573_0 := h21573c.1
                                            have p21573_1 := h21573c.2.1
                                            have p21573_2 := h21573c.2.2.1
                                            have p21573_3 := h21573c.2.2.2
                                            linarith only [hlam, p21573_0]
                                        · rcases h2bigk with h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c | h21613c
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h21285, h21531, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21613_1]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h4, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h19745, h21531, h21533, hc34, hc45, hlam, hphi, p21613_1]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h19745, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h0, hlam, p21613_1]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h21283, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h0, h19745, h21531, h21533, hc34, hc45, hlam, hphi, p21613_1]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h21286, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            rcases p21613_3 (m.d 0 2) (by simp) with h21624 | h21624
                                            · linarith only [h21624, hlam, p21613_0]
                                            · rcases p21613_3 (m.d 1 2) (by simp) with h21626 | h21626
                                              · linarith only [h21283, h21626, hlam]
                                              · rcases p21613_3 (m.d 2 3) (by simp) with h21628 | h21628
                                                · rcases p21613_3 (m.d 2 4) (by simp) with h21629 | h21629
                                                  · linarith only [h21531, h21629, hlam]
                                                  · rcases p21613_3 (m.d 2 5) (by simp) with h21631 | h21631
                                                    · linarith only [h21532, h21631, hlam]
                                                    · linarith only [h19745, h21631, hlam]
                                                · linarith only [h21628, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            rcases p21613_3 (m.d 0 2) (by simp) with h21635 | h21635
                                            · linarith only [h21635, h4, hlam]
                                            · linarith only [h0, h21635, hlam]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h21280, h21283, h21285, h21289, h4, hlam, p21613_2]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21613_1]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h19744, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h21285, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h21531, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h21533, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h0, h21285, h21531, h21533, hc34, hc45, hlam, hphi, p21613_1]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h21285, h21531, h21533, hc34, hc45, hlam, hphi, p21613_1]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [h21532, hlam, p21613_0]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            rcases p21613_3 (m.d 0 2) (by simp) with h21649 | h21649
                                            · linarith only [h19745, h21649, hlam]
                                            · linarith only [h19744, h21649, hlam]
                                          · have p21613_0 := h21613c.1
                                            have p21613_1 := h21613c.2.1
                                            have p21613_2 := h21613c.2.2.1
                                            have p21613_3 := h21613c.2.2.2
                                            linarith only [hlam, p21613_0]
                                        · rcases h2bigk with h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c | h21653c
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h21285, h21531, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21653_1]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h4, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h19745, h21531, h21533, hc34, hc45, hlam, hphi, p21653_1]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h19745, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h0, hlam, p21653_1]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h21283, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h0, h19745, h21531, h21533, hc34, hc45, hlam, hphi, p21653_1]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h21286, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            rcases p21653_3 (m.d 0 2) (by simp) with h21664 | h21664
                                            · linarith only [h21664, hlam, p21653_0]
                                            · rcases p21653_3 (m.d 1 2) (by simp) with h21666 | h21666
                                              · linarith only [h21283, h21666, hlam]
                                              · rcases p21653_3 (m.d 2 3) (by simp) with h21668 | h21668
                                                · rcases p21653_3 (m.d 2 4) (by simp) with h21669 | h21669
                                                  · linarith only [h21531, h21669, hlam]
                                                  · rcases p21653_3 (m.d 2 5) (by simp) with h21671 | h21671
                                                    · linarith only [h21532, h21671, hlam]
                                                    · linarith only [h19745, h21671, hlam]
                                                · linarith only [h21668, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            rcases p21653_3 (m.d 0 2) (by simp) with h21675 | h21675
                                            · linarith only [h21675, h4, hlam]
                                            · linarith only [h0, h21675, hlam]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h21280, h21283, h21285, h21289, h4, hlam, p21653_2]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21653_1]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h19744, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h21285, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h21531, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h21533, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h0, h21285, h21531, h21533, hc34, hc45, hlam, hphi, p21653_1]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h21285, h21531, h21533, hc34, hc45, hlam, hphi, p21653_1]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [h21532, hlam, p21653_0]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            rcases p21653_3 (m.d 0 2) (by simp) with h21689 | h21689
                                            · linarith only [h19745, h21689, hlam]
                                            · linarith only [h19744, h21689, hlam]
                                          · have p21653_0 := h21653c.1
                                            have p21653_1 := h21653c.2.1
                                            have p21653_2 := h21653c.2.2.1
                                            have p21653_3 := h21653c.2.2.2
                                            linarith only [hlam, p21653_0]
                                        · rcases h2bigk with h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c | h21693c
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h21285, h21531, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21693_1]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h4, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h19745, h21531, h21533, hc34, hc45, hlam, hphi, p21693_1]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h19745, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h0, hlam, p21693_1]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h21283, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h0, h19745, h21531, h21533, hc34, hc45, hlam, hphi, p21693_1]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h21286, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            rcases p21693_3 (m.d 0 2) (by simp) with h21704 | h21704
                                            · linarith only [h21704, hlam, p21693_0]
                                            · rcases p21693_3 (m.d 1 2) (by simp) with h21706 | h21706
                                              · linarith only [h21283, h21706, hlam]
                                              · rcases p21693_3 (m.d 2 3) (by simp) with h21708 | h21708
                                                · rcases p21693_3 (m.d 2 4) (by simp) with h21709 | h21709
                                                  · linarith only [h21531, h21709, hlam]
                                                  · rcases p21693_3 (m.d 2 5) (by simp) with h21711 | h21711
                                                    · linarith only [h21532, h21711, hlam]
                                                    · linarith only [h19745, h21711, hlam]
                                                · linarith only [h21708, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            rcases p21693_3 (m.d 0 2) (by simp) with h21715 | h21715
                                            · linarith only [h21715, h4, hlam]
                                            · linarith only [h0, h21715, hlam]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h21280, h21283, h21285, h21289, h4, hlam, p21693_2]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21693_1]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h19744, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h21285, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h21531, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h21533, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h0, h21285, h21531, h21533, hc34, hc45, hlam, hphi, p21693_1]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h21285, h21531, h21533, hc34, hc45, hlam, hphi, p21693_1]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [h21532, hlam, p21693_0]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            rcases p21693_3 (m.d 0 2) (by simp) with h21729 | h21729
                                            · linarith only [h19745, h21729, hlam]
                                            · linarith only [h19744, h21729, hlam]
                                          · have p21693_0 := h21693c.1
                                            have p21693_1 := h21693c.2.1
                                            have p21693_2 := h21693c.2.2.1
                                            have p21693_3 := h21693c.2.2.2
                                            linarith only [hlam, p21693_0]
                              · linarith only [h21562, hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h0, hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21283, hlam, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h0, h19745, h21533, hc14, hc45, hlam, hphi, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21286, hlam, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h1, hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21280, h21289, h4, hc12, hc23, hlam, hphi, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21280, h21285, h21289, h21531, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21289, hlam, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h2, hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21285, hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21288, hlam, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21529, hlam, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h3, hlam, p21537_0]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21285, h21531, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [h21280, h21283, h21285, h21289, h21531, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21537_1]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              rcases p21537_3 (m.d 0 1) (by simp) with h21752 | h21752
                              · rcases p21537_3 (m.d 1 2) (by simp) with h21753 | h21753
                                · linarith only [h21286, h21753, hlam]
                                · linarith only [h21285, h21753, hlam]
                              · linarith only [h2, h21752, hlam]
                            · have p21537_0 := h21537c.1
                              have p21537_1 := h21537c.2.1
                              have p21537_2 := h21537c.2.2.1
                              have p21537_3 := h21537c.2.2.2
                              linarith only [hlam, p21537_0]
                      · linarith only [h21280, h21532, h4, hlam]
                    · linarith only [h0, h21279, h21285, h21531, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h21279, h21281, h21283, h21285, h21288, hc24, hc45, hlam, hphi]
          · linarith only [h19744, h21285, h4, hc12, hc23, hlam, hphi]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h21762 | h21762
      · linarith only [h19744, h21280, h21762, h4, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h21764 | h21764
        · linarith only [h0, h19744, h21764, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h21766 | h21766
          · rcases m.htr 1 2 5 (by decide) (by decide) with h21767 | h21767
            · linarith only [h0, h19745, h21767, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h21769 | h21769
              · rcases m.htr 1 3 5 (by decide) (by decide) with h21770 | h21770
                · linarith only [h1, h21280, h21770, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h21772 | h21772
                  · linarith only [h2, h21762, h21772, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h21774 | h21774
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h21775 | h21775
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h21776 | h21776
                        · linarith only [h0, h21280, h21762, h21766, h21776, h4, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h21778 | h21778
                          · linarith only [h0, h21280, h21766, h21774, h21775, h21776, h21778, h4, hlam]
                          · rcases h1bigk with h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c | h21780c
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              rcases p21780_3 (m.d 0 1) (by simp) with h21782 | h21782
                              · rcases p21780_3 (m.d 1 2) (by simp) with h21783 | h21783
                                · linarith only [h21783, hlam, p21780_0]
                                · rcases p21780_3 (m.d 1 3) (by simp) with h21785 | h21785
                                  · linarith only [h1, h21785, hlam]
                                  · linarith only [h21764, h21785, hlam]
                              · linarith only [h21782, hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              rcases p21780_3 (m.d 0 1) (by simp) with h21789 | h21789
                              · rcases p21780_3 (m.d 1 2) (by simp) with h21790 | h21790
                                · linarith only [h0, h21790, hlam]
                                · rcases p21780_3 (m.d 1 3) (by simp) with h21792 | h21792
                                  · linarith only [h21792, hlam, p21780_0]
                                  · rcases p21780_3 (m.d 1 4) (by simp) with h21794 | h21794
                                    · linarith only [h2, h21794, hlam]
                                    · rcases p21780_3 (m.d 1 5) (by simp) with h21796 | h21796
                                      · linarith only [h21796, h3, hlam]
                                      · linarith only [h21770, h21796, hlam]
                              · linarith only [h21789, hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              rcases p21780_3 (m.d 0 1) (by simp) with h21800 | h21800
                              · rcases p21780_3 (m.d 1 2) (by simp) with h21801 | h21801
                                · linarith only [h0, h21801, hlam]
                                · linarith only [h21766, h21801, hlam]
                              · linarith only [h21800, hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              rcases p21780_3 (m.d 0 1) (by simp) with h21805 | h21805
                              · rcases p21780_3 (m.d 1 2) (by simp) with h21806 | h21806
                                · linarith only [h0, h21806, hlam]
                                · rcases p21780_3 (m.d 1 3) (by simp) with h21808 | h21808
                                  · linarith only [h1, h21808, hlam]
                                  · rcases p21780_3 (m.d 1 4) (by simp) with h21810 | h21810
                                    · linarith only [h2, h21810, hlam]
                                    · rcases p21780_3 (m.d 1 5) (by simp) with h21812 | h21812
                                      · linarith only [h21812, hlam, p21780_0]
                                      · rcases h1emax with h21814 | h21814 | h21814 | h21814 | h21814
                                        · linarith only [h21814, hc15, hlam, hphi, ht01, ht0b, ht5b, p21780_1]
                                        · rcases h2bigk with h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c | h21816c
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21280, h21766, h21774, h21775, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21816_1]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h4, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21280, h21774, h21775, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21816_1]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h19745, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h0, hlam, p21816_1]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21764, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21764, h21770, h21774, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21780_1, p21816_1]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21767, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            rcases p21816_3 (m.d 0 2) (by simp) with h21827 | h21827
                                            · linarith only [h21827, hlam, p21816_0]
                                            · rcases p21816_3 (m.d 1 2) (by simp) with h21829 | h21829
                                              · linarith only [h21764, h21829, hlam]
                                              · rcases p21816_3 (m.d 2 3) (by simp) with h21831 | h21831
                                                · rcases p21816_3 (m.d 2 4) (by simp) with h21832 | h21832
                                                  · linarith only [h21774, h21832, hlam]
                                                  · rcases p21816_3 (m.d 2 5) (by simp) with h21834 | h21834
                                                    · linarith only [h21775, h21834, hlam]
                                                    · linarith only [h19745, h21834, hlam]
                                                · linarith only [h21831, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            rcases p21816_3 (m.d 0 2) (by simp) with h21838 | h21838
                                            · linarith only [h21838, h4, hlam]
                                            · linarith only [h0, h21838, hlam]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h19744, h21280, h21775, h4, hlam, p21816_2]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21280, h21775, h4, hc02, hc23, hlam, hphi, p21816_1]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h19744, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21766, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21774, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21776, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h0, h21766, h21776, hc24, hc45, hlam, hphi, p21816_1]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21766, h21776, hc24, hc45, hlam, hphi, p21816_1]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [h21775, hlam, p21816_0]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            rcases p21816_3 (m.d 0 2) (by simp) with h21852 | h21852
                                            · linarith only [h19745, h21852, hlam]
                                            · linarith only [h19744, h21852, hlam]
                                          · have p21816_0 := h21816c.1
                                            have p21816_1 := h21816c.2.1
                                            have p21816_2 := h21816c.2.2.1
                                            have p21816_3 := h21816c.2.2.2
                                            linarith only [hlam, p21816_0]
                                        · rcases h2bigk with h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c | h21856c
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h21280, h21766, h21774, h4, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p21856_1]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h4, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h19745, h21774, h21776, hc34, hc45, hlam, hphi, p21856_1]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h19745, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h0, hlam, p21856_1]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h21764, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h0, h19745, h21774, h21776, hc34, hc45, hlam, hphi, p21856_1]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h21767, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            rcases p21856_3 (m.d 0 2) (by simp) with h21867 | h21867
                                            · linarith only [h21867, hlam, p21856_0]
                                            · rcases p21856_3 (m.d 1 2) (by simp) with h21869 | h21869
                                              · linarith only [h21764, h21869, hlam]
                                              · rcases p21856_3 (m.d 2 3) (by simp) with h21871 | h21871
                                                · rcases p21856_3 (m.d 2 4) (by simp) with h21872 | h21872
                                                  · linarith only [h21774, h21872, hlam]
                                                  · rcases p21856_3 (m.d 2 5) (by simp) with h21874 | h21874
                                                    · linarith only [h21775, h21874, hlam]
                                                    · linarith only [h19745, h21874, hlam]
                                                · linarith only [h21871, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            rcases p21856_3 (m.d 0 2) (by simp) with h21878 | h21878
                                            · linarith only [h21878, h4, hlam]
                                            · linarith only [h0, h21878, hlam]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h19744, h21280, h21775, h4, hlam, p21856_2]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21856_1]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h19744, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h21766, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h21774, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h21776, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h0, h21766, h21774, h21776, hc34, hc45, hlam, hphi, p21856_1]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h21766, h21774, h21776, hc34, hc45, hlam, hphi, p21856_1]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [h21775, hlam, p21856_0]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            rcases p21856_3 (m.d 0 2) (by simp) with h21892 | h21892
                                            · linarith only [h19745, h21892, hlam]
                                            · linarith only [h19744, h21892, hlam]
                                          · have p21856_0 := h21856c.1
                                            have p21856_1 := h21856c.2.1
                                            have p21856_2 := h21856c.2.2.1
                                            have p21856_3 := h21856c.2.2.2
                                            linarith only [hlam, p21856_0]
                                        · rcases h2bigk with h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c | h21896c
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h21766, h21774, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21896_1]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h4, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h21280, h21774, h21775, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21896_1]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h19745, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h0, hlam, p21896_1]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h21764, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h0, h21280, h21774, h21775, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21896_1]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h21767, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            rcases p21896_3 (m.d 0 2) (by simp) with h21907 | h21907
                                            · linarith only [h21907, hlam, p21896_0]
                                            · rcases p21896_3 (m.d 1 2) (by simp) with h21909 | h21909
                                              · linarith only [h21764, h21909, hlam]
                                              · rcases p21896_3 (m.d 2 3) (by simp) with h21911 | h21911
                                                · rcases p21896_3 (m.d 2 4) (by simp) with h21912 | h21912
                                                  · linarith only [h21774, h21912, hlam]
                                                  · rcases p21896_3 (m.d 2 5) (by simp) with h21914 | h21914
                                                    · linarith only [h21775, h21914, hlam]
                                                    · linarith only [h19745, h21914, hlam]
                                                · linarith only [h21911, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            rcases p21896_3 (m.d 0 2) (by simp) with h21918 | h21918
                                            · linarith only [h21918, h4, hlam]
                                            · linarith only [h0, h21918, hlam]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h19744, h21280, h21775, h4, hlam, p21896_2]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21896_1]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h19744, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h21766, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h21774, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h21776, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h0, h21766, h21774, h21776, hc34, hc45, hlam, hphi, p21896_1]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h21766, h21774, h21776, hc34, hc45, hlam, hphi, p21896_1]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [h21775, hlam, p21896_0]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            rcases p21896_3 (m.d 0 2) (by simp) with h21932 | h21932
                                            · linarith only [h19745, h21932, hlam]
                                            · linarith only [h19744, h21932, hlam]
                                          · have p21896_0 := h21896c.1
                                            have p21896_1 := h21896c.2.1
                                            have p21896_2 := h21896c.2.2.1
                                            have p21896_3 := h21896c.2.2.2
                                            linarith only [hlam, p21896_0]
                                        · rcases h2bigk with h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c | h21936c
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h21766, h21774, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21936_1]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h4, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h21280, h21774, h21775, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21936_1]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h19745, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h0, hlam, p21936_1]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h21764, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h0, h21280, h21774, h21775, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21936_1]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h21767, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            rcases p21936_3 (m.d 0 2) (by simp) with h21947 | h21947
                                            · linarith only [h21947, hlam, p21936_0]
                                            · rcases p21936_3 (m.d 1 2) (by simp) with h21949 | h21949
                                              · linarith only [h21764, h21949, hlam]
                                              · rcases p21936_3 (m.d 2 3) (by simp) with h21951 | h21951
                                                · rcases p21936_3 (m.d 2 4) (by simp) with h21952 | h21952
                                                  · linarith only [h21774, h21952, hlam]
                                                  · rcases p21936_3 (m.d 2 5) (by simp) with h21954 | h21954
                                                    · linarith only [h21775, h21954, hlam]
                                                    · linarith only [h19745, h21954, hlam]
                                                · linarith only [h21951, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            rcases p21936_3 (m.d 0 2) (by simp) with h21958 | h21958
                                            · linarith only [h21958, h4, hlam]
                                            · linarith only [h0, h21958, hlam]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h19744, h21280, h21775, h4, hlam, p21936_2]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h19745, hc02, hc23, hlam, hphi, p21936_1]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h19744, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h21766, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h21774, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h21776, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h0, h21766, h21774, h21776, hc34, hc45, hlam, hphi, p21936_1]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h21766, h21774, h21776, hc34, hc45, hlam, hphi, p21936_1]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [h21775, hlam, p21936_0]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            rcases p21936_3 (m.d 0 2) (by simp) with h21972 | h21972
                                            · linarith only [h19745, h21972, hlam]
                                            · linarith only [h19744, h21972, hlam]
                                          · have p21936_0 := h21936c.1
                                            have p21936_1 := h21936c.2.1
                                            have p21936_2 := h21936c.2.2.1
                                            have p21936_3 := h21936c.2.2.2
                                            linarith only [hlam, p21936_0]
                              · linarith only [h21805, hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h0, hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h21764, hlam, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h0, h21280, h21766, h21774, h21775, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h21767, hlam, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h1, hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h1, h21280, h21775, hc12, hc23, hlam, hphi, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h1, h21280, h21766, h21774, h21775, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h21770, hlam, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h2, hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h21766, hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h21769, hlam, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h21772, hlam, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h3, hlam, p21780_0]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h21766, h21774, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [h21280, h21764, h21766, h21774, h21775, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p21780_1]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              rcases p21780_3 (m.d 0 1) (by simp) with h21995 | h21995
                              · rcases p21780_3 (m.d 1 2) (by simp) with h21996 | h21996
                                · linarith only [h21767, h21996, hlam]
                                · linarith only [h21766, h21996, hlam]
                              · linarith only [h2, h21995, hlam]
                            · have p21780_0 := h21780c.1
                              have p21780_1 := h21780c.2.1
                              have p21780_2 := h21780c.2.2.1
                              have p21780_3 := h21780c.2.2.2
                              linarith only [hlam, p21780_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h22001 | h22001
                        · linarith only [h0, h21762, h21766, h21775, h22001, h4, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h22003 | h22003
                          · linarith only [h0, h21766, h21774, h21775, h22001, h22003, h4, hlam]
                          · linarith only [h0, h21766, h21775, h22003, h4, hc24, hc45, hlam, hphi]
                    · linarith only [h0, h21279, h21766, h21774, h4, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h21279, h21280, h21764, h21766, h21769, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h19744, h21766, h4, hc12, hc23, hlam, hphi]
  · linarith only [h19744, h21279, h4, hlam]

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 5 (by decide) (by decide) with h19745 | h19745
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 h19744 h19745
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 h19744 h19745

set_option maxHeartbeats 24306000 in
set_option maxHeartbeats 24306000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s21_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h19744

end R2N4
