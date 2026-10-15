import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6296000 in
set_option maxHeartbeats 6296000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s12_x0_x0_x1_x1_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg8674 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9870 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h10361 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h10362 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h10363 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11298 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11300 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11302 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h11304 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h11305 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h8674 := hg8674
  have h9870 := hg9870
  rcases m.htr 1 4 5 (by decide) (by decide) with h11306 | h11306
  · linarith only [h10363, h11306, h2, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h11308 | h11308
    · rcases m.htr 2 3 5 (by decide) (by decide) with h11309 | h11309
      · rcases m.htr 2 4 5 (by decide) (by decide) with h11310 | h11310
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11311 | h11311
          · linarith only [h1, h10363, h11304, h11311, h8674, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases h1bigk with h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c | h11313c
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              rcases p11313_3 (m.d 0 1) (by simp) with h11315 | h11315
              · rcases p11313_3 (m.d 1 2) (by simp) with h11316 | h11316
                · linarith only [h11316, hlam, p11313_0]
                · rcases p11313_3 (m.d 1 3) (by simp) with h11318 | h11318
                  · linarith only [h1, h11318, hlam]
                  · linarith only [h11298, h11318, hlam]
              · linarith only [h11315, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              rcases p11313_3 (m.d 0 1) (by simp) with h11322 | h11322
              · rcases p11313_3 (m.d 1 2) (by simp) with h11323 | h11323
                · linarith only [h0, h11323, hlam]
                · rcases p11313_3 (m.d 1 3) (by simp) with h11325 | h11325
                  · linarith only [h11325, hlam, p11313_0]
                  · rcases p11313_3 (m.d 1 4) (by simp) with h11327 | h11327
                    · linarith only [h11327, h2, hlam]
                    · rcases p11313_3 (m.d 1 5) (by simp) with h11329 | h11329
                      · linarith only [h11329, h3, hlam]
                      · rcases h3bigk with h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c | h11331c
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          rcases p11331_3 (m.d 0 3) (by simp) with h11333 | h11333
                          · rcases p11331_3 (m.d 1 3) (by simp) with h11334 | h11334
                            · linarith only [h1, h11334, hlam]
                            · rcases p11331_3 (m.d 2 3) (by simp) with h11336 | h11336
                              · rcases p11331_3 (m.d 3 4) (by simp) with h11337 | h11337
                                · linarith only [h10361, h11337, hlam]
                                · rcases p11331_3 (m.d 3 5) (by simp) with h11339 | h11339
                                  · linarith only [h10362, h11339, hlam]
                                  · rcases h5bigk with h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c | h11341c
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11300, h11306, h9870, hc12, hc25, hlam, hphi, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h9870, hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h10363, h11310, h11311, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h10363, hlam, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h3, hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11302, hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11311, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11306, hlam, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h0, h9870, hc12, hc25, hlam, hphi, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11302, hc12, hc25, hlam, hphi, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      rcases p11341_3 (m.d 0 5) (by simp) with h11355 | h11355
                                      · linarith only [h11355, h9870, hlam]
                                      · linarith only [h10362, h11355, hlam]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h0, h10363, h11308, h11310, h8674, hc12, hc23, hlam, hphi, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h10362, hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11305, hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11309, hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11311, hlam, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h0, h10363, h8674, hc12, hc45, hlam, hphi, ht23, ht34, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11300, h11305, h11306, h11311, h4, hc12, hc23, hc34, hc45, hlam, hphi, p11331_1, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11310, hlam, p11341_0]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [h11308, h11310, h11311, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11341_1]
                                    · have p11341_0 := h11341c.1
                                      have p11341_1 := h11341c.2.1
                                      have p11341_2 := h11341c.2.2.1
                                      have p11341_3 := h11341c.2.2.2
                                      linarith only [hlam, p11341_0]
                              · linarith only [h11298, h11336, hlam]
                          · linarith only [h1, h11333, hlam]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h4, hlam, p11331_1]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          rcases p11331_3 (m.d 0 3) (by simp) with h11372 | h11372
                          · rcases p11331_3 (m.d 1 3) (by simp) with h11373 | h11373
                            · linarith only [h1, h11373, hlam]
                            · linarith only [h11304, h11373, hlam]
                          · linarith only [h11372, hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          rcases p11331_3 (m.d 0 3) (by simp) with h11377 | h11377
                          · rcases p11331_3 (m.d 1 3) (by simp) with h11378 | h11378
                            · linarith only [h1, h11378, hlam]
                            · linarith only [h11305, h11378, hlam]
                          · linarith only [h11377, hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h1, hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h11298, hlam, p11331_1]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11313_1, p11331_1]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h11311, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11313_1, p11331_1]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          rcases p11331_3 (m.d 0 3) (by simp) with h11387 | h11387
                          · linarith only [h11387, h4, hlam]
                          · rcases p11331_3 (m.d 1 3) (by simp) with h11389 | h11389
                            · linarith only [h11298, h11389, hlam]
                            · rcases p11331_3 (m.d 2 3) (by simp) with h11391 | h11391
                              · rcases p11331_3 (m.d 3 4) (by simp) with h11392 | h11392
                                · linarith only [h11308, h11392, hlam]
                                · rcases p11331_3 (m.d 3 5) (by simp) with h11394 | h11394
                                  · linarith only [h11309, h11394, hlam]
                                  · rcases h5bigk with h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c | h11396c
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11300, h11306, h11308, h11310, h9870, hc12, hc23, hlam, hphi, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h9870, hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h10362, h11311, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11331_1, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h10363, hlam, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h3, hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11302, hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11311, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11306, hlam, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h0, h11308, h11310, h9870, hc12, hc23, hlam, hphi, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11302, h11308, h11310, hc12, hc23, hlam, hphi, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      rcases p11396_3 (m.d 0 5) (by simp) with h11410 | h11410
                                      · linarith only [h11410, h9870, hlam]
                                      · linarith only [h10362, h11410, hlam]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h0, h10363, h11308, h11310, h8674, hc12, hc23, hlam, hphi, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h10362, hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11305, hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11309, hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11311, hlam, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h0, h10363, h8674, hc12, hc45, hlam, hphi, ht23, ht34, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h1, h11300, h11305, h11306, h11311, hc12, hc23, hc34, hc45, hlam, hphi, p11331_1, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11310, hlam, p11396_0]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [h11308, h11310, h11311, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11396_1]
                                    · have p11396_0 := h11396c.1
                                      have p11396_1 := h11396c.2.1
                                      have p11396_2 := h11396c.2.2.1
                                      have p11396_3 := h11396c.2.2.2
                                      linarith only [hlam, p11396_0]
                              · linarith only [h11391, h4, hlam]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          rcases p11331_3 (m.d 0 3) (by simp) with h11425 | h11425
                          · linarith only [h11425, h4, hlam]
                          · linarith only [h1, h11425, hlam]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          rcases p11331_3 (m.d 0 3) (by simp) with h11429 | h11429
                          · linarith only [h11429, h4, hlam]
                          · linarith only [h10361, h11429, hlam]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          rcases p11331_3 (m.d 0 3) (by simp) with h11432 | h11432
                          · linarith only [h11432, h4, hlam]
                          · linarith only [h10362, h11432, hlam]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h10361, hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h11304, hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h11308, hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h11311, hlam, p11331_1]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h10362, hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h11305, hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h11309, hlam, p11331_0]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [h11305, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11313_1, p11331_1]
                        · have p11331_0 := h11331c.1
                          have p11331_1 := h11331c.2.1
                          have p11331_2 := h11331c.2.2.1
                          have p11331_3 := h11331c.2.2.2
                          linarith only [hlam, p11331_0]
              · linarith only [h11322, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              rcases p11313_3 (m.d 0 1) (by simp) with h11446 | h11446
              · rcases p11313_3 (m.d 1 2) (by simp) with h11447 | h11447
                · linarith only [h0, h11447, hlam]
                · rcases p11313_3 (m.d 1 3) (by simp) with h11449 | h11449
                  · linarith only [h1, h11449, hlam]
                  · linarith only [h11304, h11449, hlam]
              · linarith only [h11446, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              rcases p11313_3 (m.d 0 1) (by simp) with h11453 | h11453
              · rcases p11313_3 (m.d 1 2) (by simp) with h11454 | h11454
                · linarith only [h0, h11454, hlam]
                · rcases p11313_3 (m.d 1 3) (by simp) with h11456 | h11456
                  · linarith only [h1, h11456, hlam]
                  · linarith only [h11305, h11456, hlam]
              · linarith only [h11453, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h0, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h11298, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h11300, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h11302, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h1, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              rcases p11313_3 (m.d 0 1) (by simp) with h11466 | h11466
              · rcases p11313_3 (m.d 1 2) (by simp) with h11467 | h11467
                · linarith only [h11298, h11467, hlam]
                · rcases p11313_3 (m.d 1 3) (by simp) with h11469 | h11469
                  · rcases p11313_3 (m.d 1 4) (by simp) with h11470 | h11470
                    · linarith only [h11304, h11470, hlam]
                    · linarith only [h11300, h11470, hlam]
                  · linarith only [h11298, h11469, hlam]
              · linarith only [h0, h11466, hlam]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              rcases p11313_3 (m.d 0 1) (by simp) with h11476 | h11476
              · rcases p11313_3 (m.d 1 2) (by simp) with h11477 | h11477
                · linarith only [h11298, h11477, hlam]
                · rcases p11313_3 (m.d 1 3) (by simp) with h11479 | h11479
                  · rcases p11313_3 (m.d 1 4) (by simp) with h11480 | h11480
                    · linarith only [h11304, h11480, hlam]
                    · rcases p11313_3 (m.d 1 5) (by simp) with h11482 | h11482
                      · linarith only [h11305, h11482, hlam]
                      · linarith only [h11306, h11482, hlam]
                  · linarith only [h11304, h11479, hlam]
              · linarith only [h11476, h2, hlam]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              rcases p11313_3 (m.d 0 1) (by simp) with h11487 | h11487
              · rcases p11313_3 (m.d 1 2) (by simp) with h11488 | h11488
                · linarith only [h11298, h11488, hlam]
                · rcases p11313_3 (m.d 1 3) (by simp) with h11490 | h11490
                  · rcases p11313_3 (m.d 1 4) (by simp) with h11491 | h11491
                    · linarith only [h11304, h11491, hlam]
                    · rcases p11313_3 (m.d 1 5) (by simp) with h11493 | h11493
                      · linarith only [h11305, h11493, hlam]
                      · rcases h3bigk with h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c | h11495c
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h11306, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b, p11313_1, p11495_1]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h4, hlam, p11495_1]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          rcases p11495_3 (m.d 0 3) (by simp) with h11499 | h11499
                          · rcases p11495_3 (m.d 1 3) (by simp) with h11500 | h11500
                            · linarith only [h1, h11500, hlam]
                            · linarith only [h11304, h11500, hlam]
                          · linarith only [h11499, hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          rcases p11495_3 (m.d 0 3) (by simp) with h11504 | h11504
                          · rcases p11495_3 (m.d 1 3) (by simp) with h11505 | h11505
                            · linarith only [h1, h11505, hlam]
                            · linarith only [h11305, h11505, hlam]
                          · linarith only [h11504, hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h1, hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h11298, hlam, p11495_1]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          rcases p11495_3 (m.d 0 3) (by simp) with h11512 | h11512
                          · rcases p11495_3 (m.d 1 3) (by simp) with h11513 | h11513
                            · rcases p11495_3 (m.d 2 3) (by simp) with h11514 | h11514
                              · rcases p11495_3 (m.d 3 4) (by simp) with h11515 | h11515
                                · linarith only [h11515, hlam, p11495_0]
                                · rcases p11495_3 (m.d 3 5) (by simp) with h11517 | h11517
                                  · linarith only [h11305, h11517, hlam]
                                  · linarith only [h11311, h11517, hlam]
                              · linarith only [h11308, h11514, hlam]
                            · linarith only [h11513, hlam, p11495_0]
                          · linarith only [h10361, h11512, hlam]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          rcases p11495_3 (m.d 0 3) (by simp) with h11523 | h11523
                          · rcases p11495_3 (m.d 1 3) (by simp) with h11524 | h11524
                            · rcases p11495_3 (m.d 2 3) (by simp) with h11525 | h11525
                              · rcases p11495_3 (m.d 3 4) (by simp) with h11526 | h11526
                                · linarith only [h11304, h11526, hlam]
                                · rcases p11495_3 (m.d 3 5) (by simp) with h11528 | h11528
                                  · linarith only [h11528, hlam, p11495_0]
                                  · rcases h5bigk with h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c | h11530c
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11300, h11306, h11308, h11310, h9870, hc12, hc23, hlam, hphi, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h9870, hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h10363, h11308, h11310, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h10363, hlam, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h3, hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11302, hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p11313_1, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11306, hlam, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11300, h11306, h11308, h11310, h3, hc12, hc23, hlam, hphi, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11300, h11306, h11308, h11310, hc12, hc23, hlam, hphi, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      rcases p11530_3 (m.d 0 5) (by simp) with h11544 | h11544
                                      · linarith only [h11544, h9870, hlam]
                                      · linarith only [h10362, h11544, hlam]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h0, h10363, h11308, h11310, h8674, hc12, hc23, hlam, hphi, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h10362, hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11305, hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11309, hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11311, hlam, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11300, h11306, h3, hc12, hc45, hlam, hphi, ht23, ht34, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11300, h11306, hc12, hc45, hlam, hphi, ht23, ht34, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h11310, hlam, p11530_0]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [h1, h11300, h11306, h11308, h11310, h11311, hc01, hc12, hc23, hc34, hlam, hphi, ht0b, ht45, ht5b, p11313_1, p11530_1]
                                    · have p11530_0 := h11530c.1
                                      have p11530_1 := h11530c.2.1
                                      have p11530_2 := h11530c.2.2.1
                                      have p11530_3 := h11530c.2.2.2
                                      linarith only [hlam, p11530_0]
                              · linarith only [h11309, h11525, hlam]
                            · linarith only [h11524, hlam, p11495_0]
                          · linarith only [h10362, h11523, hlam]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h1, h11300, h11306, hc12, hc23, hlam, hphi, p11313_1, p11495_1]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h11300, h11306, hc12, hc23, hlam, hphi, p11313_1, p11495_1]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          rcases p11495_3 (m.d 0 3) (by simp) with h11564 | h11564
                          · linarith only [h11564, h4, hlam]
                          · linarith only [h10361, h11564, hlam]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          rcases p11495_3 (m.d 0 3) (by simp) with h11567 | h11567
                          · linarith only [h11567, h4, hlam]
                          · linarith only [h10362, h11567, hlam]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h10361, hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h11304, hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h11308, hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h11311, hlam, p11495_1]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h10362, hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h11305, hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h11309, hlam, p11495_0]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [h1, h11305, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11495_1]
                        · have p11495_0 := h11495c.1
                          have p11495_1 := h11495c.2.1
                          have p11495_2 := h11495c.2.2.1
                          have p11495_3 := h11495c.2.2.2
                          linarith only [hlam, p11495_0]
                  · linarith only [h11305, h11490, hlam]
              · linarith only [h11487, h3, hlam]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h2, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h10363, h11306, h11308, h11310, h3, hc12, hc23, hlam, hphi, p11313_1]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h11304, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h11306, hlam, p11313_1]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h3, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h10363, h11308, h11310, h3, hc12, hc23, hlam, hphi, p11313_1]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h11305, hlam, p11313_0]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [h10363, h11300, h11308, h11310, h3, hc12, hc23, hlam, hphi, p11313_1]
            · have p11313_0 := h11313c.1
              have p11313_1 := h11313c.2.1
              have p11313_2 := h11313c.2.2.1
              have p11313_3 := h11313c.2.2.2
              linarith only [hlam, p11313_0]
        · rcases m.htr 3 4 5 (by decide) (by decide) with h11592 | h11592
          · linarith only [h0, h11310, h11592, h8674, hc12, hc34, hlam, hphi, ht23]
          · rcases h1bigk with h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c | h11594c
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              rcases p11594_3 (m.d 0 1) (by simp) with h11596 | h11596
              · rcases p11594_3 (m.d 1 2) (by simp) with h11597 | h11597
                · linarith only [h11597, hlam, p11594_0]
                · rcases p11594_3 (m.d 1 3) (by simp) with h11599 | h11599
                  · linarith only [h1, h11599, hlam]
                  · linarith only [h11298, h11599, hlam]
              · linarith only [h11596, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              rcases p11594_3 (m.d 0 1) (by simp) with h11603 | h11603
              · rcases p11594_3 (m.d 1 2) (by simp) with h11604 | h11604
                · linarith only [h0, h11604, hlam]
                · rcases p11594_3 (m.d 1 3) (by simp) with h11606 | h11606
                  · linarith only [h11606, hlam, p11594_0]
                  · rcases p11594_3 (m.d 1 4) (by simp) with h11608 | h11608
                    · linarith only [h11608, h2, hlam]
                    · rcases p11594_3 (m.d 1 5) (by simp) with h11610 | h11610
                      · linarith only [h11610, h3, hlam]
                      · rcases h3bigk with h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c | h11612c
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          rcases p11612_3 (m.d 0 3) (by simp) with h11614 | h11614
                          · rcases p11612_3 (m.d 1 3) (by simp) with h11615 | h11615
                            · linarith only [h1, h11615, hlam]
                            · rcases p11612_3 (m.d 2 3) (by simp) with h11617 | h11617
                              · rcases p11612_3 (m.d 3 4) (by simp) with h11618 | h11618
                                · linarith only [h10361, h11618, hlam]
                                · rcases p11612_3 (m.d 3 5) (by simp) with h11620 | h11620
                                  · linarith only [h10362, h11620, hlam]
                                  · rcases h5bigk with h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c | h11622c
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11302, h11310, h9870, hc12, hc45, hlam, hphi, ht23, ht34, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h9870, hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11310, h11592, h9870, hc34, hc45, hlam, hphi, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h10363, hlam, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h3, hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11302, hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11592, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11306, hlam, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11305, h11310, h11592, h4, h9870, hc02, hc23, hc34, hc45, hlam, hphi, p11612_1, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11302, h11305, h11310, h11592, h4, hc12, hc23, hc34, hc45, hlam, hphi, p11612_1, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11310, h11592, hc34, hc45, hlam, hphi, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11310, hlam, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h10362, hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11305, hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11309, hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [hlam, p11622_0]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11592, hlam, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h10363, h11300, h11305, h11592, h2, h4, hc12, hc23, hc34, hc45, hlam, hphi, p11612_1, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11300, h11305, h11306, h11592, h4, hc12, hc23, hc34, hc45, hlam, hphi, p11612_1, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h0, h11305, h11592, h4, h9870, hc12, hc23, hc34, hc45, hlam, hphi, p11612_1, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [h11592, hc34, hc45, hlam, hphi, p11622_1]
                                    · have p11622_0 := h11622c.1
                                      have p11622_1 := h11622c.2.1
                                      have p11622_2 := h11622c.2.2.1
                                      have p11622_3 := h11622c.2.2.2
                                      linarith only [hlam, p11622_0]
                              · linarith only [h11298, h11617, hlam]
                          · linarith only [h1, h11614, hlam]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h4, hlam, p11612_1]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          rcases p11612_3 (m.d 0 3) (by simp) with h11651 | h11651
                          · rcases p11612_3 (m.d 1 3) (by simp) with h11652 | h11652
                            · linarith only [h1, h11652, hlam]
                            · linarith only [h11304, h11652, hlam]
                          · linarith only [h11651, hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          rcases p11612_3 (m.d 0 3) (by simp) with h11656 | h11656
                          · rcases p11612_3 (m.d 1 3) (by simp) with h11657 | h11657
                            · linarith only [h1, h11657, hlam]
                            · linarith only [h11305, h11657, hlam]
                          · linarith only [h11656, hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h1, hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h11298, hlam, p11612_1]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11594_1, p11612_1]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h11592, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11594_1, p11612_1]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          rcases p11612_3 (m.d 0 3) (by simp) with h11666 | h11666
                          · linarith only [h11666, h4, hlam]
                          · rcases p11612_3 (m.d 1 3) (by simp) with h11668 | h11668
                            · linarith only [h11298, h11668, hlam]
                            · rcases p11612_3 (m.d 2 3) (by simp) with h11670 | h11670
                              · rcases p11612_3 (m.d 3 4) (by simp) with h11671 | h11671
                                · linarith only [h11308, h11671, hlam]
                                · rcases p11612_3 (m.d 3 5) (by simp) with h11673 | h11673
                                  · linarith only [h11309, h11673, hlam]
                                  · rcases h5bigk with h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c | h11675c
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11300, h11306, h9870, hc12, hc25, hlam, hphi, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h9870, hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h10362, h11592, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p11612_1, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h10363, hlam, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h3, hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11302, hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11592, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11306, hlam, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h0, h9870, hc12, hc25, hlam, hphi, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11302, hc12, hc25, hlam, hphi, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11310, h11592, hc34, hc45, hlam, hphi, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11310, hlam, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h10362, hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11305, hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11309, hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [hlam, p11675_0]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11592, hlam, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h10363, h11300, h2, hc12, hc45, hlam, hphi, ht23, ht34, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h1, h11300, h11305, h11306, h11592, hc12, hc23, hc34, hc45, hlam, hphi, p11612_1, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h0, h1, h11305, h11592, h9870, hc12, hc23, hc34, hc45, hlam, hphi, p11612_1, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [h11592, hc34, hc45, hlam, hphi, p11675_1]
                                    · have p11675_0 := h11675c.1
                                      have p11675_1 := h11675c.2.1
                                      have p11675_2 := h11675c.2.2.1
                                      have p11675_3 := h11675c.2.2.2
                                      linarith only [hlam, p11675_0]
                              · linarith only [h11670, h4, hlam]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          rcases p11612_3 (m.d 0 3) (by simp) with h11702 | h11702
                          · linarith only [h11702, h4, hlam]
                          · linarith only [h1, h11702, hlam]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          rcases p11612_3 (m.d 0 3) (by simp) with h11706 | h11706
                          · linarith only [h11706, h4, hlam]
                          · linarith only [h10361, h11706, hlam]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          rcases p11612_3 (m.d 0 3) (by simp) with h11709 | h11709
                          · linarith only [h11709, h4, hlam]
                          · linarith only [h10362, h11709, hlam]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h10361, hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h11304, hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h11308, hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h11592, hlam, p11612_1]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h10362, hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h11305, hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h11309, hlam, p11612_0]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [h11305, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11594_1, p11612_1]
                        · have p11612_0 := h11612c.1
                          have p11612_1 := h11612c.2.1
                          have p11612_2 := h11612c.2.2.1
                          have p11612_3 := h11612c.2.2.2
                          linarith only [hlam, p11612_0]
              · linarith only [h11603, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              rcases p11594_3 (m.d 0 1) (by simp) with h11723 | h11723
              · rcases p11594_3 (m.d 1 2) (by simp) with h11724 | h11724
                · linarith only [h0, h11724, hlam]
                · rcases p11594_3 (m.d 1 3) (by simp) with h11726 | h11726
                  · linarith only [h1, h11726, hlam]
                  · linarith only [h11304, h11726, hlam]
              · linarith only [h11723, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              rcases p11594_3 (m.d 0 1) (by simp) with h11730 | h11730
              · rcases p11594_3 (m.d 1 2) (by simp) with h11731 | h11731
                · linarith only [h0, h11731, hlam]
                · rcases p11594_3 (m.d 1 3) (by simp) with h11733 | h11733
                  · linarith only [h1, h11733, hlam]
                  · linarith only [h11305, h11733, hlam]
              · linarith only [h11730, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h0, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h11298, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h11300, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h11302, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h1, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              rcases p11594_3 (m.d 0 1) (by simp) with h11743 | h11743
              · rcases p11594_3 (m.d 1 2) (by simp) with h11744 | h11744
                · linarith only [h11298, h11744, hlam]
                · rcases p11594_3 (m.d 1 3) (by simp) with h11746 | h11746
                  · rcases p11594_3 (m.d 1 4) (by simp) with h11747 | h11747
                    · linarith only [h11304, h11747, hlam]
                    · linarith only [h11300, h11747, hlam]
                  · linarith only [h11298, h11746, hlam]
              · linarith only [h0, h11743, hlam]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              rcases p11594_3 (m.d 0 1) (by simp) with h11753 | h11753
              · rcases p11594_3 (m.d 1 2) (by simp) with h11754 | h11754
                · linarith only [h11298, h11754, hlam]
                · rcases p11594_3 (m.d 1 3) (by simp) with h11756 | h11756
                  · rcases p11594_3 (m.d 1 4) (by simp) with h11757 | h11757
                    · linarith only [h11304, h11757, hlam]
                    · rcases p11594_3 (m.d 1 5) (by simp) with h11759 | h11759
                      · linarith only [h11305, h11759, hlam]
                      · linarith only [h11306, h11759, hlam]
                  · linarith only [h11304, h11756, hlam]
              · linarith only [h11753, h2, hlam]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              rcases p11594_3 (m.d 0 1) (by simp) with h11764 | h11764
              · rcases p11594_3 (m.d 1 2) (by simp) with h11765 | h11765
                · linarith only [h11298, h11765, hlam]
                · rcases p11594_3 (m.d 1 3) (by simp) with h11767 | h11767
                  · rcases p11594_3 (m.d 1 4) (by simp) with h11768 | h11768
                    · linarith only [h11304, h11768, hlam]
                    · rcases p11594_3 (m.d 1 5) (by simp) with h11770 | h11770
                      · linarith only [h11305, h11770, hlam]
                      · rcases h3bigk with h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c | h11772c
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h11300, h11306, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11594_1, p11772_1]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h4, hlam, p11772_1]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          rcases p11772_3 (m.d 0 3) (by simp) with h11776 | h11776
                          · rcases p11772_3 (m.d 1 3) (by simp) with h11777 | h11777
                            · linarith only [h1, h11777, hlam]
                            · linarith only [h11304, h11777, hlam]
                          · linarith only [h11776, hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          rcases p11772_3 (m.d 0 3) (by simp) with h11781 | h11781
                          · rcases p11772_3 (m.d 1 3) (by simp) with h11782 | h11782
                            · linarith only [h1, h11782, hlam]
                            · linarith only [h11305, h11782, hlam]
                          · linarith only [h11781, hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h1, hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h11298, hlam, p11772_1]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          rcases p11772_3 (m.d 0 3) (by simp) with h11789 | h11789
                          · rcases p11772_3 (m.d 1 3) (by simp) with h11790 | h11790
                            · rcases p11772_3 (m.d 2 3) (by simp) with h11791 | h11791
                              · rcases p11772_3 (m.d 3 4) (by simp) with h11792 | h11792
                                · linarith only [h11792, hlam, p11772_0]
                                · rcases p11772_3 (m.d 3 5) (by simp) with h11794 | h11794
                                  · linarith only [h11305, h11794, hlam]
                                  · linarith only [h11592, h11794, hlam]
                              · linarith only [h11308, h11791, hlam]
                            · linarith only [h11790, hlam, p11772_0]
                          · linarith only [h10361, h11789, hlam]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          rcases p11772_3 (m.d 0 3) (by simp) with h11800 | h11800
                          · rcases p11772_3 (m.d 1 3) (by simp) with h11801 | h11801
                            · rcases p11772_3 (m.d 2 3) (by simp) with h11802 | h11802
                              · rcases p11772_3 (m.d 3 4) (by simp) with h11803 | h11803
                                · linarith only [h11304, h11803, hlam]
                                · rcases p11772_3 (m.d 3 5) (by simp) with h11805 | h11805
                                  · linarith only [h11805, hlam, p11772_0]
                                  · rcases h5bigk with h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c | h11807c
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11300, h11306, h9870, hc12, hc25, hlam, hphi, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h9870, hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11310, h11592, h9870, hc34, hc45, hlam, hphi, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h10363, hlam, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h3, hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11302, hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p11594_1, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11306, hlam, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h0, h11310, h9870, hc12, hc45, hlam, hphi, ht23, ht34, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11302, h11310, hc12, hc45, hlam, hphi, ht23, ht34, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11310, h11592, hc34, hc45, hlam, hphi, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11310, hlam, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h10362, hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11305, hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11309, hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [hlam, p11807_0]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11592, hlam, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h10363, h11300, h2, hc12, hc45, hlam, hphi, ht23, ht34, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11300, h11306, hc12, hc45, hlam, hphi, ht23, ht34, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h0, h9870, hc12, hc45, hlam, hphi, ht23, ht34, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [h11592, hc34, hc45, hlam, hphi, p11807_1]
                                    · have p11807_0 := h11807c.1
                                      have p11807_1 := h11807c.2.1
                                      have p11807_2 := h11807c.2.2.1
                                      have p11807_3 := h11807c.2.2.2
                                      linarith only [hlam, p11807_0]
                              · linarith only [h11309, h11802, hlam]
                            · linarith only [h11801, hlam, p11772_0]
                          · linarith only [h10362, h11800, hlam]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h1, h11300, h11306, hc12, hc23, hlam, hphi, p11594_1, p11772_1]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h11300, h11306, hc12, hc23, hlam, hphi, p11594_1, p11772_1]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          rcases p11772_3 (m.d 0 3) (by simp) with h11839 | h11839
                          · linarith only [h11839, h4, hlam]
                          · linarith only [h10361, h11839, hlam]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          rcases p11772_3 (m.d 0 3) (by simp) with h11842 | h11842
                          · linarith only [h11842, h4, hlam]
                          · linarith only [h10362, h11842, hlam]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h10361, hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h11304, hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h11308, hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h11592, hlam, p11772_1]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h10362, hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h11305, hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h11309, hlam, p11772_0]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [h1, h11305, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11772_1]
                        · have p11772_0 := h11772c.1
                          have p11772_1 := h11772c.2.1
                          have p11772_2 := h11772c.2.2.1
                          have p11772_3 := h11772c.2.2.2
                          linarith only [hlam, p11772_0]
                  · linarith only [h11305, h11767, hlam]
              · linarith only [h11764, h3, hlam]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h2, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h10363, h2, hc12, hc45, hlam, hphi, ht23, ht34, p11594_1]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h11304, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h11306, hlam, p11594_1]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h3, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              rcases p11594_3 (m.d 0 1) (by simp) with h11863 | h11863
              · rcases p11594_3 (m.d 1 2) (by simp) with h11864 | h11864
                · linarith only [h11302, h11864, hlam]
                · rcases p11594_3 (m.d 1 3) (by simp) with h11866 | h11866
                  · rcases p11594_3 (m.d 1 4) (by simp) with h11867 | h11867
                    · linarith only [h11306, h11867, hlam]
                    · linarith only [h11300, h11867, hlam]
                  · linarith only [h11298, h11866, hlam]
              · linarith only [h0, h11863, hlam]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [h11305, hlam, p11594_0]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              rcases p11594_3 (m.d 0 1) (by simp) with h11873 | h11873
              · rcases p11594_3 (m.d 1 2) (by simp) with h11874 | h11874
                · linarith only [h11302, h11874, hlam]
                · rcases p11594_3 (m.d 1 3) (by simp) with h11876 | h11876
                  · rcases p11594_3 (m.d 1 4) (by simp) with h11877 | h11877
                    · linarith only [h11306, h11877, hlam]
                    · rcases p11594_3 (m.d 1 5) (by simp) with h11879 | h11879
                      · rcases h3bigk with h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c | h11880c
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h11300, h11305, h4, hc12, hc23, hlam, hphi, p11594_1, p11880_1]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h4, hlam, p11880_1]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          rcases p11880_3 (m.d 0 3) (by simp) with h11884 | h11884
                          · rcases p11880_3 (m.d 1 3) (by simp) with h11885 | h11885
                            · linarith only [h1, h11885, hlam]
                            · linarith only [h11304, h11885, hlam]
                          · linarith only [h11884, hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          rcases p11880_3 (m.d 0 3) (by simp) with h11889 | h11889
                          · rcases p11880_3 (m.d 1 3) (by simp) with h11890 | h11890
                            · linarith only [h1, h11890, hlam]
                            · linarith only [h11305, h11890, hlam]
                          · linarith only [h11889, hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h1, hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h11298, hlam, p11880_1]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          rcases p11880_3 (m.d 0 3) (by simp) with h11897 | h11897
                          · rcases p11880_3 (m.d 1 3) (by simp) with h11898 | h11898
                            · rcases p11880_3 (m.d 2 3) (by simp) with h11899 | h11899
                              · rcases p11880_3 (m.d 3 4) (by simp) with h11900 | h11900
                                · linarith only [h11900, hlam, p11880_0]
                                · rcases p11880_3 (m.d 3 5) (by simp) with h11902 | h11902
                                  · linarith only [h11305, h11902, hlam]
                                  · linarith only [h11592, h11902, hlam]
                              · linarith only [h11308, h11899, hlam]
                            · linarith only [h11898, hlam, p11880_0]
                          · linarith only [h10361, h11897, hlam]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          rcases p11880_3 (m.d 0 3) (by simp) with h11908 | h11908
                          · rcases p11880_3 (m.d 1 3) (by simp) with h11909 | h11909
                            · rcases p11880_3 (m.d 2 3) (by simp) with h11910 | h11910
                              · rcases p11880_3 (m.d 3 4) (by simp) with h11911 | h11911
                                · linarith only [h11304, h11911, hlam]
                                · rcases p11880_3 (m.d 3 5) (by simp) with h11913 | h11913
                                  · linarith only [h11913, hlam, p11880_0]
                                  · rcases h5bigk with h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c | h11915c
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11300, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11594_1, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h9870, hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11310, h11592, h9870, hc34, hc45, hlam, hphi, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h10363, hlam, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h3, hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11302, hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11592, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11306, hlam, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h0, h11310, h9870, hc12, hc45, hlam, hphi, ht23, ht34, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11302, h11310, hc12, hc45, hlam, hphi, ht23, ht34, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11310, h11592, hc34, hc45, hlam, hphi, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11310, hlam, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h10362, hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11305, hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11309, hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [hlam, p11915_0]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11592, hlam, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11300, h3, hc12, hc45, hlam, hphi, ht23, ht34, p11594_1, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11300, hc12, hc45, hlam, hphi, ht23, ht34, p11594_1, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h0, h9870, hc12, hc45, hlam, hphi, ht23, ht34, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [h11592, hc34, hc45, hlam, hphi, p11915_1]
                                    · have p11915_0 := h11915c.1
                                      have p11915_1 := h11915c.2.1
                                      have p11915_2 := h11915c.2.2.1
                                      have p11915_3 := h11915c.2.2.2
                                      linarith only [hlam, p11915_0]
                              · linarith only [h11309, h11910, hlam]
                            · linarith only [h11909, hlam, p11880_0]
                          · linarith only [h10362, h11908, hlam]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h10362, h11300, h3, hc12, hc23, hlam, hphi, p11594_1, p11880_1]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h11300, h11305, hc12, hc23, hlam, hphi, p11594_1, p11880_1]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          rcases p11880_3 (m.d 0 3) (by simp) with h11947 | h11947
                          · linarith only [h11947, h4, hlam]
                          · linarith only [h10361, h11947, hlam]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          rcases p11880_3 (m.d 0 3) (by simp) with h11950 | h11950
                          · linarith only [h11950, h4, hlam]
                          · linarith only [h10362, h11950, hlam]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h10361, hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h11304, hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h11308, hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h11592, hlam, p11880_1]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h10362, hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h11305, hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h11309, hlam, p11880_0]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [h1, h11305, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p11880_1]
                        · have p11880_0 := h11880c.1
                          have p11880_1 := h11880c.2.1
                          have p11880_2 := h11880c.2.2.1
                          have p11880_3 := h11880c.2.2.2
                          linarith only [hlam, p11880_0]
                      · linarith only [h11306, h11879, hlam]
                  · linarith only [h11304, h11876, hlam]
              · linarith only [h11873, h2, hlam]
            · have p11594_0 := h11594c.1
              have p11594_1 := h11594c.2.1
              have p11594_2 := h11594c.2.2.1
              have p11594_3 := h11594c.2.2.2
              linarith only [hlam, p11594_0]
      · linarith only [h1, h11305, h11309, h4, hlam]
    · linarith only [h10361, h11308, h4, hlam]

end R2N4
