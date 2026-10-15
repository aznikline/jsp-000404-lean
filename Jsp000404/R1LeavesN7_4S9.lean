import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 12030000 in
set_option maxHeartbeats 12030000 in
theorem r1l7_11_23_L_I_H_I_s5_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4375 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4725 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h4726 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 4 (by decide) (by decide) with h5314 | h5314
  · rcases m.htr 1 2 5 (by decide) (by decide) with h5315 | h5315
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5316 | h5316
      · linarith only [h1, h5316, h6, hlam]
      · linarith only [h4726, h5314, h5316, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5319 | h5319
      · linarith only [h1, h5319, h6, hlam]
      · linarith only [h4726, h5314, h5319, hlam]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h5322 | h5322
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5323 | h5323
      · linarith only [h4, h4726, h5322, h5323, h6, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5325 | h5325
        · linarith only [h4, h4375, h4726, h5325, hlam]
        · linarith only [h4726, h5322, h5325, hlam]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h5328 | h5328
      · linarith only [h1, h4, h4726, h5328, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h5330 | h5330
        · linarith only [h4, h4375, h4726, h5330, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h5332 | h5332
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5333 | h5333
            · linarith only [h4, h5333, h6, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5335 | h5335
              · linarith only [h4, h4375, h5335, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5337 | h5337
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5338 | h5338
                  · rcases h1bigk with h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c | h5339c
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      rcases p5339_3 (m.d 0 1) (by simp) with h5341 | h5341
                      · rcases p5339_3 (m.d 1 2) (by simp) with h5342 | h5342
                        · linarith only [h5342, hlam, p5339_0]
                        · rcases p5339_3 (m.d 1 3) (by simp) with h5344 | h5344
                          · linarith only [h1, h5344, hlam]
                          · linarith only [h4726, h5344, hlam]
                      · linarith only [h5341, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      rcases p5339_3 (m.d 0 1) (by simp) with h5348 | h5348
                      · rcases p5339_3 (m.d 1 2) (by simp) with h5349 | h5349
                        · linarith only [h0, h5349, hlam]
                        · rcases p5339_3 (m.d 1 3) (by simp) with h5351 | h5351
                          · linarith only [h5351, hlam, p5339_0]
                          · rcases p5339_3 (m.d 1 4) (by simp) with h5353 | h5353
                            · linarith only [h2, h5353, hlam]
                            · linarith only [h5328, h5353, hlam]
                      · linarith only [h5348, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      rcases p5339_3 (m.d 0 1) (by simp) with h5357 | h5357
                      · rcases p5339_3 (m.d 1 2) (by simp) with h5358 | h5358
                        · linarith only [h0, h5358, hlam]
                        · rcases p5339_3 (m.d 1 3) (by simp) with h5360 | h5360
                          · linarith only [h1, h5360, hlam]
                          · rcases p5339_3 (m.d 1 4) (by simp) with h5362 | h5362
                            · linarith only [h5362, hlam, p5339_0]
                            · rcases p5339_3 (m.d 1 5) (by simp) with h5364 | h5364
                              · linarith only [h3, h5364, hlam]
                              · rcases h3bigk with h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c | h5366c
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h4375, h4726, h5338, hc12, hc34, hlam, hphi, ht23, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h4375, h4726, h5338, hc12, hc34, hlam, hphi, ht23, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h6, hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h4375, hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h1, hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h4726, hlam, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h5328, hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h5330, hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h4, hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h4726, hc12, hc23, hlam, hphi, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h5333, hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h5335, hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h4726, hc12, hc34, hlam, hphi, ht23, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [hc23, hc34, hlam, hphi, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h1, h4375, h4726, hc12, hc34, hlam, hphi, ht23, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h1, h4726, hc12, hc35, hlam, hphi, ht23, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h4726, hc12, hc35, hlam, hphi, ht23, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h4726, hc12, hc35, hlam, hphi, ht23, p5366_1]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [h5338, hlam, p5366_0]
                                · have p5366_0 := h5366c.1
                                  have p5366_1 := h5366c.2.1
                                  have p5366_2 := h5366c.2.2.1
                                  have p5366_3 := h5366c.2.2.2
                                  linarith only [hlam, p5366_0]
                      · linarith only [h5357, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      rcases p5339_3 (m.d 0 1) (by simp) with h5393 | h5393
                      · rcases p5339_3 (m.d 1 2) (by simp) with h5394 | h5394
                        · linarith only [h0, h5394, hlam]
                        · rcases p5339_3 (m.d 1 3) (by simp) with h5396 | h5396
                          · linarith only [h1, h5396, hlam]
                          · rcases p5339_3 (m.d 1 4) (by simp) with h5398 | h5398
                            · linarith only [h2, h5398, hlam]
                            · linarith only [h5332, h5398, hlam]
                      · linarith only [h5393, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h0, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h4726, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h5314, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h5322, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h1, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h1, h6, hc12, hc34, hlam, hphi, ht23, p5339_1]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h5328, hlam, p5339_1]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h5330, hlam, p5339_1]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h2, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      rcases p5339_3 (m.d 0 1) (by simp) with h5413 | h5413
                      · rcases p5339_3 (m.d 1 2) (by simp) with h5414 | h5414
                        · linarith only [h5314, h5414, hlam]
                        · rcases p5339_3 (m.d 1 3) (by simp) with h5416 | h5416
                          · linarith only [h5328, h5416, hlam]
                          · linarith only [h4726, h5416, hlam]
                      · linarith only [h0, h5413, hlam]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      rcases p5339_3 (m.d 0 1) (by simp) with h5420 | h5420
                      · rcases p5339_3 (m.d 1 2) (by simp) with h5421 | h5421
                        · linarith only [h5314, h5421, hlam]
                        · rcases p5339_3 (m.d 1 3) (by simp) with h5423 | h5423
                          · linarith only [h5328, h5423, hlam]
                          · rcases p5339_3 (m.d 1 4) (by simp) with h5425 | h5425
                            · rcases p5339_3 (m.d 1 5) (by simp) with h5426 | h5426
                              · linarith only [h5332, h5426, hlam]
                              · linarith only [h5330, h5426, hlam]
                            · linarith only [h5328, h5425, hlam]
                      · linarith only [h1, h5420, hlam]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      rcases p5339_3 (m.d 0 1) (by simp) with h5432 | h5432
                      · rcases p5339_3 (m.d 1 2) (by simp) with h5433 | h5433
                        · linarith only [h5314, h5433, hlam]
                        · rcases p5339_3 (m.d 1 3) (by simp) with h5435 | h5435
                          · linarith only [h5328, h5435, hlam]
                          · rcases p5339_3 (m.d 1 4) (by simp) with h5437 | h5437
                            · rcases p5339_3 (m.d 1 5) (by simp) with h5438 | h5438
                              · linarith only [h5332, h5438, hlam]
                              · rcases h3bigk with h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c | h5440c
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4375, h4726, h5338, hc12, hc34, hlam, hphi, ht23, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4375, h5338, hc23, hc34, hlam, hphi, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h6, hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4375, hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h1, hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4726, hlam, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h5328, hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h5330, hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4, hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4726, hc12, hc23, hlam, hphi, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h5333, hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h5335, hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4726, hc12, hc34, hlam, hphi, ht23, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4726, hc12, hc34, hlam, hphi, ht23, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4, h4375, h4726, hc12, hc34, hlam, hphi, ht23, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4, h4726, hc12, hc35, hlam, hphi, ht23, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4726, hc12, hc35, hlam, hphi, ht23, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h4726, hc12, hc35, hlam, hphi, ht23, p5440_1]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [h5338, hlam, p5440_0]
                                · have p5440_0 := h5440c.1
                                  have p5440_1 := h5440c.2.1
                                  have p5440_2 := h5440c.2.2.1
                                  have p5440_3 := h5440c.2.2.2
                                  linarith only [hlam, p5440_0]
                            · linarith only [h5332, h5437, hlam]
                      · linarith only [h3, h5432, hlam]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h3, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      rcases p5339_3 (m.d 0 1) (by simp) with h5469 | h5469
                      · rcases p5339_3 (m.d 1 2) (by simp) with h5470 | h5470
                        · linarith only [h5322, h5470, hlam]
                        · rcases p5339_3 (m.d 1 3) (by simp) with h5472 | h5472
                          · linarith only [h5330, h5472, hlam]
                          · linarith only [h4726, h5472, hlam]
                      · linarith only [h0, h5469, hlam]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      rcases p5339_3 (m.d 0 1) (by simp) with h5476 | h5476
                      · rcases p5339_3 (m.d 1 2) (by simp) with h5477 | h5477
                        · linarith only [h5322, h5477, hlam]
                        · rcases p5339_3 (m.d 1 3) (by simp) with h5479 | h5479
                          · linarith only [h5330, h5479, hlam]
                          · rcases p5339_3 (m.d 1 4) (by simp) with h5481 | h5481
                            · rcases p5339_3 (m.d 1 5) (by simp) with h5482 | h5482
                              · rcases h3bigk with h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c | h5483c
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4726, h6, hc12, hc34, hlam, hphi, ht23, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4726, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h6, hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4375, hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h1, hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4726, hlam, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h5328, hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h5330, hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4, hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4726, hc12, hc23, hlam, hphi, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h5333, hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h5335, hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4726, hc12, hc34, hlam, hphi, ht23, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4726, hc12, hc34, hlam, hphi, ht23, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4, h4375, h4726, hc12, hc34, hlam, hphi, ht23, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4, h4726, hc12, hc35, hlam, hphi, ht23, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4726, hc12, hc35, hlam, hphi, ht23, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h4726, hc12, hc35, hlam, hphi, ht23, p5483_1]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [h5338, hlam, p5483_0]
                                · have p5483_0 := h5483c.1
                                  have p5483_1 := h5483c.2.1
                                  have p5483_2 := h5483c.2.2.1
                                  have p5483_3 := h5483c.2.2.2
                                  linarith only [hlam, p5483_0]
                              · linarith only [h5330, h5482, hlam]
                            · linarith only [h5328, h5481, hlam]
                      · linarith only [h1, h5476, hlam]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [h5332, hlam, p5339_0]
                    · have p5339_0 := h5339c.1
                      have p5339_1 := h5339c.2.1
                      have p5339_2 := h5339c.2.2.1
                      have p5339_3 := h5339c.2.2.2
                      linarith only [hlam, p5339_0]
                  · linarith only [h2, h5332, h5338, h6, hlam]
                · linarith only [h4725, h5314, h5337, h6, hc12, hc34, hlam, hphi, ht23]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h5516 | h5516
            · linarith only [h4, h5516, h6, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h5518 | h5518
              · linarith only [h4, h4375, h5518, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h5520 | h5520
                · rcases m.htr 3 4 5 (by decide) (by decide) with h5521 | h5521
                  · rcases h1bigk with h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c | h5522c
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, h4726, h5, h5328, h5332, h5520, hlam, p5522_2]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, h5, h5328, h5332, h5520, hlam, p5522_2]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, h5, h5332, h5520, hlam, p5522_2]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      rcases p5522_3 (m.d 0 1) (by simp) with h5527 | h5527
                      · rcases p5522_3 (m.d 1 2) (by simp) with h5528 | h5528
                        · linarith only [h0, h5528, hlam]
                        · rcases p5522_3 (m.d 1 3) (by simp) with h5530 | h5530
                          · linarith only [h1, h5530, hlam]
                          · rcases p5522_3 (m.d 1 4) (by simp) with h5532 | h5532
                            · linarith only [h2, h5532, hlam]
                            · rcases p5522_3 (m.d 1 5) (by simp) with h5534 | h5534
                              · linarith only [h5534, hlam, p5522_0]
                              · rcases h3bigk with h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c | h5536c
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4375, h4726, hc12, hc35, hlam, hphi, ht23, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4375, h4726, hc12, hc35, hlam, hphi, ht23, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h6, hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4375, hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h1, hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4726, hlam, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h5328, hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h5330, hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4, hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4726, hc12, hc23, hlam, hphi, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h5516, hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h5518, hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [hc03, hc34, hlam, hphi, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4726, hc12, hc34, hlam, hphi, ht23, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4726, hc12, hc34, hlam, hphi, ht23, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4, h4375, h4726, hc12, hc34, hlam, hphi, ht23, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4, h4726, hc12, hc35, hlam, hphi, ht23, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4726, hc12, hc35, hlam, hphi, ht23, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h4726, hc12, hc35, hlam, hphi, ht23, p5536_1]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [h5521, hlam, p5536_0]
                                · have p5536_0 := h5536c.1
                                  have p5536_1 := h5536c.2.1
                                  have p5536_2 := h5536c.2.2.1
                                  have p5536_3 := h5536c.2.2.2
                                  linarith only [hlam, p5536_0]
                      · linarith only [h5527, hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h4726, hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h5314, hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h5322, hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h1, hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, h5, h5328, h5332, h5520, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5522_1]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h5328, hlam, p5522_1]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h5330, hlam, p5522_1]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h2, hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, h5, h5332, h5520, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5522_1]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, h5, h5332, h5520, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5522_1]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h5332, hlam, p5522_1]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h3, hlam, p5522_0]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, h5, h5332, h5520, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5522_1]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, h4726, h5, h5332, h5520, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5522_1]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [h0, h5, h5332, h5520, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p5522_1]
                    · have p5522_0 := h5522c.1
                      have p5522_1 := h5522c.2.1
                      have p5522_2 := h5522c.2.2.1
                      have p5522_3 := h5522c.2.2.2
                      linarith only [hlam, p5522_0]
                  · linarith only [h0, h4, h4726, h5, h5520, h5521, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                · linarith only [h4725, h5314, h5520, h6, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 12030000 in
set_option maxHeartbeats 12030000 in
theorem r1l7_11_23_L_I_H_I_s5_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4375 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4725 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 3 (by decide) (by decide) with h4726 | h4726
  · exact r1l7_11_23_L_I_H_I_s5_x1_x1_x0_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 h6 h4375 h4725 h4726
  · exact r1l7_11_23_L_I_H_I_s5_x1_x1_x0_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg5 h6 h4375 h4725 h4726

set_option maxHeartbeats 12030000 in
set_option maxHeartbeats 12030000 in
theorem r1l7_11_23_L_I_H_I_s5_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4375 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h4725 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 1 2 3 (by decide) (by decide) with h5585 | h5585
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5586 | h5586
    · rcases m.htr 1 2 5 (by decide) (by decide) with h5587 | h5587
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5588 | h5588
        · linarith only [h1, h5588, h6, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5590 | h5590
          · linarith only [h1, h4375, h5590, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5592 | h5592
            · linarith only [h2, h4725, h5592, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5594 | h5594
              · linarith only [h1, h5585, h5594, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5596 | h5596
                · linarith only [h1, h4375, h5585, h5596, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5598 | h5598
                  · linarith only [h0, h4725, h5586, h5598, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5600 | h5600
                    · rcases h1bigk with h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c | h5601c
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        rcases p5601_3 (m.d 0 1) (by simp) with h5603 | h5603
                        · rcases p5601_3 (m.d 1 2) (by simp) with h5604 | h5604
                          · linarith only [h5604, hlam, p5601_0]
                          · rcases p5601_3 (m.d 1 3) (by simp) with h5606 | h5606
                            · linarith only [h1, h5606, hlam]
                            · rcases p5601_3 (m.d 1 4) (by simp) with h5608 | h5608
                              · linarith only [h2, h5608, hlam]
                              · rcases p5601_3 (m.d 1 5) (by simp) with h5610 | h5610
                                · linarith only [h3, h5610, hlam]
                                · rcases h3bigk with h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c | h5612c
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h4725, h5585, h5600, h6, hc23, hc34, hlam, hphi, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h4725, h5600, h6, hc23, hc34, hlam, hphi, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h6, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h4375, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h1, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h5588, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h5590, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h4, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h5585, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h5594, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h5596, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [hc03, hc34, hlam, hphi, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h5585, hc23, hc34, hlam, hphi, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [hc23, hc34, hlam, hphi, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h4725, h5600, hc04, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h1, h5585, hc23, hc35, hlam, hphi, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h5585, hc23, hc35, hlam, hphi, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [hc23, hc35, hlam, hphi, p5612_1]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [h5600, hlam, p5612_0]
                                  · have p5612_0 := h5612c.1
                                    have p5612_1 := h5612c.2.1
                                    have p5612_2 := h5612c.2.2.1
                                    have p5612_3 := h5612c.2.2.2
                                    linarith only [hlam, p5612_0]
                        · linarith only [h5603, hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        rcases p5601_3 (m.d 0 1) (by simp) with h5639 | h5639
                        · rcases p5601_3 (m.d 1 2) (by simp) with h5640 | h5640
                          · linarith only [h0, h5640, hlam]
                          · linarith only [h5585, h5640, hlam]
                        · linarith only [h5639, hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        rcases p5601_3 (m.d 0 1) (by simp) with h5644 | h5644
                        · rcases p5601_3 (m.d 1 2) (by simp) with h5645 | h5645
                          · linarith only [h0, h5645, hlam]
                          · linarith only [h5586, h5645, hlam]
                        · linarith only [h5644, hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        rcases p5601_3 (m.d 0 1) (by simp) with h5649 | h5649
                        · rcases p5601_3 (m.d 1 2) (by simp) with h5650 | h5650
                          · linarith only [h0, h5650, hlam]
                          · linarith only [h5587, h5650, hlam]
                        · linarith only [h5649, hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h0, hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        rcases p5601_3 (m.d 0 1) (by simp) with h5656 | h5656
                        · rcases p5601_3 (m.d 1 2) (by simp) with h5657 | h5657
                          · rcases p5601_3 (m.d 1 3) (by simp) with h5658 | h5658
                            · linarith only [h5585, h5658, hlam]
                            · rcases p5601_3 (m.d 1 4) (by simp) with h5660 | h5660
                              · linarith only [h5586, h5660, hlam]
                              · linarith only [h5588, h5660, hlam]
                          · linarith only [h5585, h5657, hlam]
                        · linarith only [h1, h5656, hlam]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        rcases p5601_3 (m.d 0 1) (by simp) with h5665 | h5665
                        · rcases p5601_3 (m.d 1 2) (by simp) with h5666 | h5666
                          · rcases p5601_3 (m.d 1 3) (by simp) with h5667 | h5667
                            · linarith only [h5585, h5667, hlam]
                            · rcases p5601_3 (m.d 1 4) (by simp) with h5669 | h5669
                              · linarith only [h5586, h5669, hlam]
                              · rcases p5601_3 (m.d 1 5) (by simp) with h5671 | h5671
                                · linarith only [h5587, h5671, hlam]
                                · linarith only [h5592, h5671, hlam]
                          · linarith only [h5586, h5666, hlam]
                        · linarith only [h2, h5665, hlam]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        rcases p5601_3 (m.d 0 1) (by simp) with h5676 | h5676
                        · rcases p5601_3 (m.d 1 2) (by simp) with h5677 | h5677
                          · rcases p5601_3 (m.d 1 3) (by simp) with h5678 | h5678
                            · linarith only [h5585, h5678, hlam]
                            · rcases p5601_3 (m.d 1 4) (by simp) with h5680 | h5680
                              · linarith only [h5586, h5680, hlam]
                              · rcases p5601_3 (m.d 1 5) (by simp) with h5682 | h5682
                                · linarith only [h5587, h5682, hlam]
                                · rcases h3bigk with h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c | h5684c
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h4725, h5585, h6, hc23, hc45, hlam, hphi, ht34, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h4725, h6, hc23, hc45, hlam, hphi, ht34, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h6, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h4375, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h1, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h5588, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h5590, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h4, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h5585, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h5594, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h5596, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [hc03, hc34, hlam, hphi, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h5585, hc23, hc34, hlam, hphi, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [hc23, hc34, hlam, hphi, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h3, h4375, h5587, h5594, h5598, hc23, hc34, hlam, hphi, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h1, h5585, hc23, hc35, hlam, hphi, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h5585, hc23, hc35, hlam, hphi, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [hc23, hc35, hlam, hphi, p5684_1]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [h5600, hlam, p5684_0]
                                  · have p5684_0 := h5684c.1
                                    have p5684_1 := h5684c.2.1
                                    have p5684_2 := h5684c.2.2.1
                                    have p5684_3 := h5684c.2.2.2
                                    linarith only [hlam, p5684_0]
                          · linarith only [h5587, h5677, hlam]
                        · linarith only [h3, h5676, hlam]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h1, hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h5585, hlam, p5601_1]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h5588, hlam, p5601_1]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h5590, hlam, p5601_1]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h2, hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h5586, hlam, p5601_1]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h2, h4725, h5585, hc23, hc45, hlam, hphi, ht34, p5601_1]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h5592, hlam, p5601_1]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h3, hlam, p5601_0]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h5587, hlam, p5601_1]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h3, h4725, h5585, h5600, hc23, hc34, hlam, hphi, p5601_1]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [h3, h4725, h5586, h5594, h5600, hc23, hc34, hlam, hphi, p5601_1]
                      · have p5601_0 := h5601c.1
                        have p5601_1 := h5601c.2.1
                        have p5601_2 := h5601c.2.2.1
                        have p5601_3 := h5601c.2.2.2
                        linarith only [hlam, p5601_0]
                    · rcases h1bigk with h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        rcases p5727_3 (m.d 0 1) (by simp) with h5729 | h5729
                        · rcases p5727_3 (m.d 1 2) (by simp) with h5730 | h5730
                          · linarith only [h5730, hlam, p5727_0]
                          · rcases p5727_3 (m.d 1 3) (by simp) with h5732 | h5732
                            · linarith only [h1, h5732, hlam]
                            · rcases p5727_3 (m.d 1 4) (by simp) with h5734 | h5734
                              · linarith only [h2, h5734, hlam]
                              · rcases p5727_3 (m.d 1 5) (by simp) with h5736 | h5736
                                · linarith only [h3, h5736, hlam]
                                · rcases h3bigk with h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c | h5738c
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5585, h6, hc23, hc34, hlam, hphi, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5600, h6, hc23, hc45, hlam, hphi, ht34, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h6, hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h4375, hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h1, hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5588, hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5590, hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h4, hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5585, hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5594, hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5596, hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5600, hc03, hc45, hlam, hphi, ht34, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5585, h5600, hc23, hc45, hlam, hphi, ht34, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5600, hc23, hc45, hlam, hphi, ht34, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [hlam, p5738_0]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5600, hlam, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h1, h5585, hc23, hc35, hlam, hphi, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5585, hc23, hc35, hlam, hphi, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [hc23, hc35, hlam, hphi, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [h5600, hc34, hc45, hlam, hphi, p5738_1]
                                  · have p5738_0 := h5738c.1
                                    have p5738_1 := h5738c.2.1
                                    have p5738_2 := h5738c.2.2.1
                                    have p5738_3 := h5738c.2.2.2
                                    linarith only [hlam, p5738_0]
                        · linarith only [h5729, hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        rcases p5727_3 (m.d 0 1) (by simp) with h5765 | h5765
                        · rcases p5727_3 (m.d 1 2) (by simp) with h5766 | h5766
                          · linarith only [h0, h5766, hlam]
                          · linarith only [h5585, h5766, hlam]
                        · linarith only [h5765, hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        rcases p5727_3 (m.d 0 1) (by simp) with h5770 | h5770
                        · rcases p5727_3 (m.d 1 2) (by simp) with h5771 | h5771
                          · linarith only [h0, h5771, hlam]
                          · linarith only [h5586, h5771, hlam]
                        · linarith only [h5770, hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        rcases p5727_3 (m.d 0 1) (by simp) with h5775 | h5775
                        · rcases p5727_3 (m.d 1 2) (by simp) with h5776 | h5776
                          · linarith only [h0, h5776, hlam]
                          · linarith only [h5587, h5776, hlam]
                        · linarith only [h5775, hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h0, hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        rcases p5727_3 (m.d 0 1) (by simp) with h5782 | h5782
                        · rcases p5727_3 (m.d 1 2) (by simp) with h5783 | h5783
                          · rcases p5727_3 (m.d 1 3) (by simp) with h5784 | h5784
                            · linarith only [h5585, h5784, hlam]
                            · rcases p5727_3 (m.d 1 4) (by simp) with h5786 | h5786
                              · linarith only [h5586, h5786, hlam]
                              · linarith only [h5588, h5786, hlam]
                          · linarith only [h5585, h5783, hlam]
                        · linarith only [h1, h5782, hlam]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        rcases p5727_3 (m.d 0 1) (by simp) with h5791 | h5791
                        · rcases p5727_3 (m.d 1 2) (by simp) with h5792 | h5792
                          · rcases p5727_3 (m.d 1 3) (by simp) with h5793 | h5793
                            · linarith only [h5585, h5793, hlam]
                            · rcases p5727_3 (m.d 1 4) (by simp) with h5795 | h5795
                              · linarith only [h5586, h5795, hlam]
                              · rcases p5727_3 (m.d 1 5) (by simp) with h5797 | h5797
                                · linarith only [h5587, h5797, hlam]
                                · linarith only [h5592, h5797, hlam]
                          · linarith only [h5586, h5792, hlam]
                        · linarith only [h2, h5791, hlam]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        rcases p5727_3 (m.d 0 1) (by simp) with h5802 | h5802
                        · rcases p5727_3 (m.d 1 2) (by simp) with h5803 | h5803
                          · rcases p5727_3 (m.d 1 3) (by simp) with h5804 | h5804
                            · linarith only [h5585, h5804, hlam]
                            · rcases p5727_3 (m.d 1 4) (by simp) with h5806 | h5806
                              · linarith only [h5586, h5806, hlam]
                              · rcases p5727_3 (m.d 1 5) (by simp) with h5808 | h5808
                                · linarith only [h5587, h5808, hlam]
                                · rcases h3bigk with h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c | h5810c
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5585, h5600, h6, hc23, hc45, hlam, hphi, ht34, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5600, h6, hc23, hc45, hlam, hphi, ht34, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h6, hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h4375, hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h1, hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5588, hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5590, hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h4, hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5585, hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5594, hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5596, hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5600, hc03, hc45, hlam, hphi, ht34, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5600, hc13, hc45, hlam, hphi, ht34, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5600, hc23, hc45, hlam, hphi, ht34, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [hlam, p5810_0]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5600, hlam, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5600, hc03, hc45, hlam, hphi, ht34, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5585, h5600, hc23, hc45, hlam, hphi, ht34, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5600, hc23, hc45, hlam, hphi, ht34, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [h5600, h6, hc04, hc45, hlam, hphi, p5810_1]
                                  · have p5810_0 := h5810c.1
                                    have p5810_1 := h5810c.2.1
                                    have p5810_2 := h5810c.2.2.1
                                    have p5810_3 := h5810c.2.2.2
                                    linarith only [hlam, p5810_0]
                          · linarith only [h5587, h5803, hlam]
                        · linarith only [h3, h5802, hlam]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h1, hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h5585, hlam, p5727_1]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h5588, hlam, p5727_1]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h5590, hlam, p5727_1]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h2, hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h5586, hlam, p5727_1]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h2, h4725, h5585, hc23, hc45, hlam, hphi, ht34, p5727_1]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h5592, hlam, p5727_1]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h3, hlam, p5727_0]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [h5587, hlam, p5727_1]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        rcases p5727_3 (m.d 0 1) (by simp) with h5850 | h5850
                        · rcases p5727_3 (m.d 1 2) (by simp) with h5851 | h5851
                          · rcases p5727_3 (m.d 1 3) (by simp) with h5852 | h5852
                            · linarith only [h5590, h5852, hlam]
                            · rcases p5727_3 (m.d 1 4) (by simp) with h5854 | h5854
                              · linarith only [h5592, h5854, hlam]
                              · linarith only [h5588, h5854, hlam]
                          · linarith only [h5585, h5851, hlam]
                        · linarith only [h1, h5850, hlam]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        rcases p5727_3 (m.d 0 1) (by simp) with h5859 | h5859
                        · rcases p5727_3 (m.d 1 2) (by simp) with h5860 | h5860
                          · rcases p5727_3 (m.d 1 3) (by simp) with h5861 | h5861
                            · linarith only [h5590, h5861, hlam]
                            · rcases p5727_3 (m.d 1 4) (by simp) with h5863 | h5863
                              · linarith only [h5592, h5863, hlam]
                              · rcases p5727_3 (m.d 1 5) (by simp) with h5865 | h5865
                                · rcases h3bigk with h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c | h5866c
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5585, h5600, h6, hc23, hc45, hlam, hphi, ht34, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5600, h6, hc23, hc45, hlam, hphi, ht34, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h6, hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h4375, hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h1, hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5588, hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5590, hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h4, hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5585, hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5594, hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5596, hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5600, hc03, hc45, hlam, hphi, ht34, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5585, h5600, hc23, hc45, hlam, hphi, ht34, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5600, hc23, hc45, hlam, hphi, ht34, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [hlam, p5866_0]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5600, hlam, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h1, h5585, h5600, hc23, hc45, hlam, hphi, ht34, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5585, h5600, hc23, hc45, hlam, hphi, ht34, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5600, hc23, hc45, hlam, hphi, ht34, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [h5600, h6, hc04, hc45, hlam, hphi, p5866_1]
                                  · have p5866_0 := h5866c.1
                                    have p5866_1 := h5866c.2.1
                                    have p5866_2 := h5866c.2.2.1
                                    have p5866_3 := h5866c.2.2.2
                                    linarith only [hlam, p5866_0]
                                · linarith only [h5592, h5865, hlam]
                          · linarith only [h5586, h5860, hlam]
                        · linarith only [h2, h5859, hlam]
                      · have p5727_0 := h5727c.1
                        have p5727_1 := h5727c.2.1
                        have p5727_2 := h5727c.2.2.1
                        have p5727_3 := h5727c.2.2.2
                        linarith only [hlam, p5727_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h5896 | h5896
        · linarith only [h1, h5896, h6, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h5898 | h5898
          · linarith only [h1, h4375, h5898, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h5900 | h5900
            · linarith only [h2, h4725, h5900, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h5902 | h5902
              · linarith only [h1, h5585, h5902, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h5904 | h5904
                · linarith only [h1, h4375, h5585, h5904, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h5906 | h5906
                  · linarith only [h4725, h5586, h5587, h5906, h6, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h5908 | h5908
                    · linarith only [h5585, h5587, h5906, h5908, hc23, hc34, hlam, hphi]
                    · rcases h1bigk with h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c | h5910c
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        rcases p5910_3 (m.d 0 1) (by simp) with h5912 | h5912
                        · rcases p5910_3 (m.d 1 2) (by simp) with h5913 | h5913
                          · linarith only [h5913, hlam, p5910_0]
                          · rcases p5910_3 (m.d 1 3) (by simp) with h5915 | h5915
                            · linarith only [h1, h5915, hlam]
                            · rcases p5910_3 (m.d 1 4) (by simp) with h5917 | h5917
                              · linarith only [h2, h5917, hlam]
                              · rcases p5910_3 (m.d 1 5) (by simp) with h5919 | h5919
                                · linarith only [h3, h5919, hlam]
                                · linarith only [h5587, h5919, hlam]
                        · linarith only [h5912, hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        rcases p5910_3 (m.d 0 1) (by simp) with h5923 | h5923
                        · rcases p5910_3 (m.d 1 2) (by simp) with h5924 | h5924
                          · linarith only [h0, h5924, hlam]
                          · linarith only [h5585, h5924, hlam]
                        · linarith only [h5923, hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        rcases p5910_3 (m.d 0 1) (by simp) with h5928 | h5928
                        · rcases p5910_3 (m.d 1 2) (by simp) with h5929 | h5929
                          · linarith only [h0, h5929, hlam]
                          · linarith only [h5586, h5929, hlam]
                        · linarith only [h5928, hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        rcases p5910_3 (m.d 0 1) (by simp) with h5933 | h5933
                        · rcases p5910_3 (m.d 1 2) (by simp) with h5934 | h5934
                          · linarith only [h0, h5934, hlam]
                          · rcases p5910_3 (m.d 1 3) (by simp) with h5936 | h5936
                            · linarith only [h1, h5936, hlam]
                            · rcases p5910_3 (m.d 1 4) (by simp) with h5938 | h5938
                              · linarith only [h2, h5938, hlam]
                              · rcases p5910_3 (m.d 1 5) (by simp) with h5940 | h5940
                                · linarith only [h5940, hlam, p5910_0]
                                · rcases h3bigk with h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c | h5942c
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5585, h6, hc23, hc34, hlam, hphi, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5908, h6, hc23, hc45, hlam, hphi, ht34, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h6, hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h4375, hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h1, hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h1, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5896, hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5898, hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h4, hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5585, hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5902, hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5904, hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5908, hc03, hc45, hlam, hphi, ht34, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5585, h5908, hc23, hc45, hlam, hphi, ht34, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5908, hc23, hc45, hlam, hphi, ht34, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [hlam, p5942_0]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5908, hlam, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h1, h5585, hc23, hc35, hlam, hphi, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5585, hc23, hc35, hlam, hphi, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [hc23, hc35, hlam, hphi, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [h5908, hc34, hc45, hlam, hphi, p5942_1]
                                  · have p5942_0 := h5942c.1
                                    have p5942_1 := h5942c.2.1
                                    have p5942_2 := h5942c.2.2.1
                                    have p5942_3 := h5942c.2.2.2
                                    linarith only [hlam, p5942_0]
                        · linarith only [h5933, hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h0, hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h5585, h5587, h5904, h5908, hc23, hc45, hlam, hphi, ht34, p5910_1]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h5585, h5587, h5896, h5904, h5908, hc23, hc45, hlam, hphi, ht34, p5910_1]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h5587, hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h1, hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h5585, hlam, p5910_1]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h5896, hlam, p5910_1]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h5898, hlam, p5910_1]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h2, hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h5586, hlam, p5910_1]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h2, h4725, h5585, hc23, hc45, hlam, hphi, ht34, p5910_1]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h5900, hlam, p5910_1]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h3, hlam, p5910_0]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [h3, h4375, h5585, h5908, hc23, hc45, hlam, hphi, ht34, p5910_1]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        rcases p5910_3 (m.d 0 1) (by simp) with h5986 | h5986
                        · rcases p5910_3 (m.d 1 2) (by simp) with h5987 | h5987
                          · linarith only [h5587, h5987, hlam]
                          · linarith only [h5585, h5987, hlam]
                        · linarith only [h1, h5986, hlam]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        rcases p5910_3 (m.d 0 1) (by simp) with h5991 | h5991
                        · rcases p5910_3 (m.d 1 2) (by simp) with h5992 | h5992
                          · linarith only [h5587, h5992, hlam]
                          · linarith only [h5586, h5992, hlam]
                        · linarith only [h2, h5991, hlam]
                      · have p5910_0 := h5910c.1
                        have p5910_1 := h5910c.2.1
                        have p5910_2 := h5910c.2.2.1
                        have p5910_3 := h5910c.2.2.2
                        linarith only [hlam, p5910_0]
    · linarith only [h4725, h5, h5585, h5586, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h5998 | h5998
    · linarith only [h4, h4725, h5585, h5998, h6, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h6000 | h6000
      · rcases m.htr 1 3 4 (by decide) (by decide) with h6001 | h6001
        · linarith only [h4, h5585, h6, h6000, h6001, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6003 | h6003
          · linarith only [h4, h4375, h5585, h6000, h6003, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
          · linarith only [h5585, h6000, h6003, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h6006 | h6006
        · linarith only [h1, h4, h5585, h6, h6006, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h6008 | h6008
          · linarith only [h4, h4375, h5585, h6008, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h6010 | h6010
            · linarith only [h4725, h5, h5998, h6010, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h6012 | h6012
              · linarith only [h4, h6, h6012, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h6014 | h6014
                · linarith only [h4, h4375, h6014, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h6016 | h6016
                  · linarith only [h4725, h5, h6016, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h6018 | h6018
                    · linarith only [h4, h4725, h5585, h6, h6018, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h4, h5585, h6, h6018, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
