import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5520000 in
set_option maxHeartbeats 5520000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s10_x1_x1_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h4553 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h5072 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h6397 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h6398 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h6399 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  rcases m.htr 1 3 4 (by decide) (by decide) with h6400 | h6400
  · linarith only [h1, h6400, h7, hlam]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h6402 | h6402
    · linarith only [h1, h4553, h6402, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h6404 | h6404
      · linarith only [h2, h5072, h6404, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h6406 | h6406
        · linarith only [h1, h6397, h6406, h7, hlam]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h6408 | h6408
          · linarith only [h1, h4553, h6397, h6408, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h6410 | h6410
            · linarith only [h5, h5072, h6410, hlam]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h6412 | h6412
              · rcases h0bigk with h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c | h6413c
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [hlam, p6413_0]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  rcases p6413_3 (m.d 0 1) (by simp) with h6415 | h6415
                  · rcases p6413_3 (m.d 0 2) (by simp) with h6416 | h6416
                    · linarith only [h0, h6416, hlam]
                    · rcases p6413_3 (m.d 0 3) (by simp) with h6418 | h6418
                      · linarith only [h1, h6418, hlam]
                      · rcases p6413_3 (m.d 0 4) (by simp) with h6420 | h6420
                        · linarith only [h2, h6420, hlam]
                        · rcases p6413_3 (m.d 0 5) (by simp) with h6422 | h6422
                          · linarith only [h3, h6422, hlam]
                          · rcases h2bigk with h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c | h6424c
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6410, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h0, hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h0, h6410, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h4, hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6397, hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6406, hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6408, hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h5, hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6398, hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6410, hlam, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6, hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6399, hlam, p6424_0]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6413_1, p6424_1]
                            · have p6424_0 := h6424c.1
                              have p6424_1 := h6424c.2.1
                              have p6424_2 := h6424c.2.2.1
                              have p6424_3 := h6424c.2.2.2
                              linarith only [hlam, p6424_0]
                  · linarith only [h0, h6415, hlam]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  rcases p6413_3 (m.d 0 1) (by simp) with h6451 | h6451
                  · rcases p6413_3 (m.d 0 2) (by simp) with h6452 | h6452
                    · linarith only [h0, h6452, hlam]
                    · linarith only [h4, h6452, hlam]
                  · linarith only [h1, h6451, hlam]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  rcases p6413_3 (m.d 0 1) (by simp) with h6456 | h6456
                  · rcases p6413_3 (m.d 0 2) (by simp) with h6457 | h6457
                    · linarith only [h0, h6457, hlam]
                    · linarith only [h5, h6457, hlam]
                  · linarith only [h2, h6456, hlam]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  rcases p6413_3 (m.d 0 1) (by simp) with h6461 | h6461
                  · rcases p6413_3 (m.d 0 2) (by simp) with h6462 | h6462
                    · linarith only [h0, h6462, hlam]
                    · linarith only [h6, h6462, hlam]
                  · linarith only [h3, h6461, hlam]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h0, hlam, p6413_0]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [hlam, p6413_0]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  rcases p6413_3 (m.d 0 1) (by simp) with h6468 | h6468
                  · rcases p6413_3 (m.d 0 2) (by simp) with h6469 | h6469
                    · rcases p6413_3 (m.d 0 3) (by simp) with h6470 | h6470
                      · linarith only [h4, h6470, hlam]
                      · rcases p6413_3 (m.d 0 4) (by simp) with h6472 | h6472
                        · linarith only [h5, h6472, hlam]
                        · linarith only [h6472, h7, hlam]
                    · linarith only [h4, h6469, hlam]
                  · linarith only [h1, h6468, hlam]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  rcases p6413_3 (m.d 0 1) (by simp) with h6477 | h6477
                  · rcases p6413_3 (m.d 0 2) (by simp) with h6478 | h6478
                    · rcases p6413_3 (m.d 0 3) (by simp) with h6479 | h6479
                      · linarith only [h4, h6479, hlam]
                      · rcases p6413_3 (m.d 0 4) (by simp) with h6481 | h6481
                        · linarith only [h5, h6481, hlam]
                        · rcases p6413_3 (m.d 0 5) (by simp) with h6483 | h6483
                          · linarith only [h6, h6483, hlam]
                          · linarith only [h5072, h6483, hlam]
                    · linarith only [h5, h6478, hlam]
                  · linarith only [h2, h6477, hlam]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  rcases p6413_3 (m.d 0 1) (by simp) with h6488 | h6488
                  · rcases p6413_3 (m.d 0 2) (by simp) with h6489 | h6489
                    · rcases p6413_3 (m.d 0 3) (by simp) with h6490 | h6490
                      · linarith only [h4, h6490, hlam]
                      · rcases p6413_3 (m.d 0 4) (by simp) with h6492 | h6492
                        · linarith only [h5, h6492, hlam]
                        · rcases p6413_3 (m.d 0 5) (by simp) with h6494 | h6494
                          · linarith only [h6, h6494, hlam]
                          · rcases h2bigk with h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c | h6496c
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              rcases p6496_3 (m.d 0 2) (by simp) with h6498 | h6498
                              · rcases p6496_3 (m.d 1 2) (by simp) with h6499 | h6499
                                · linarith only [h0, h6499, hlam]
                                · rcases p6496_3 (m.d 2 3) (by simp) with h6501 | h6501
                                  · linarith only [h4, h6501, hlam]
                                  · rcases p6496_3 (m.d 2 4) (by simp) with h6503 | h6503
                                    · linarith only [h5, h6503, hlam]
                                    · rcases p6496_3 (m.d 2 5) (by simp) with h6505 | h6505
                                      · linarith only [h6, h6505, hlam]
                                      · rcases h3bigk with h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h6397, h7, hc23, hc34, hlam, hphi, p6507_1]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h7, hc23, hc34, hlam, hphi, p6507_1]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h7, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h4553, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h1, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h1, h7, hc23, hc34, hlam, hphi, p6507_1]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h6400, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h6402, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h4, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h6397, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h6406, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h6408, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          rcases p6507_3 (m.d 0 3) (by simp) with h6523 | h6523
                                          · linarith only [h6523, hlam, p6507_0]
                                          · rcases p6507_3 (m.d 1 3) (by simp) with h6525 | h6525
                                            · linarith only [h6400, h6525, hlam]
                                            · rcases p6507_3 (m.d 2 3) (by simp) with h6527 | h6527
                                              · linarith only [h6406, h6527, hlam]
                                              · rcases p6507_3 (m.d 3 4) (by simp) with h6529 | h6529
                                                · rcases p6507_3 (m.d 3 5) (by simp) with h6530 | h6530
                                                  · linarith only [h6412, h6530, hlam]
                                                  · linarith only [h4553, h6530, hlam]
                                                · linarith only [h6529, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          rcases p6507_3 (m.d 0 3) (by simp) with h6534 | h6534
                                          · linarith only [h6534, h7, hlam]
                                          · linarith only [h1, h6534, hlam]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          rcases p6507_3 (m.d 0 3) (by simp) with h6537 | h6537
                                          · linarith only [h6537, h7, hlam]
                                          · linarith only [h4, h6537, hlam]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h5072, h6412, h7, hc03, hc34, hlam, hphi, p6507_1]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          rcases p6507_3 (m.d 0 3) (by simp) with h6542 | h6542
                                          · linarith only [h6542, hlam, p6507_0]
                                          · rcases p6507_3 (m.d 1 3) (by simp) with h6544 | h6544
                                            · linarith only [h6402, h6544, hlam]
                                            · rcases p6507_3 (m.d 2 3) (by simp) with h6546 | h6546
                                              · linarith only [h6408, h6546, hlam]
                                              · rcases p6507_3 (m.d 3 4) (by simp) with h6548 | h6548
                                                · rcases p6507_3 (m.d 3 5) (by simp) with h6549 | h6549
                                                  · rcases h5bigk with h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c | h6550c
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [hlam, p6550_0]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h0, hc01, hc15, hlam, hphi, ht0b, ht5b, p6413_1, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h0, h6406, h6410, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h4553, hlam, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h5072, hlam, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h3, hlam, p6550_0]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [hlam, p6550_0]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h3, h6406, h6410, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6402, hlam, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6404, hlam, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6, hlam, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6399, hlam, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [hlam, p6550_0]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6408, hlam, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6410, hlam, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6399, h6406, h6410, hc23, hc35, hlam, hphi, p6413_2, p6496_1, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6399, h6406, h6410, hc23, hc35, hlam, hphi, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6406, h6410, hc23, hc35, hlam, hphi, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [hlam, p6550_0]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h1, h5072, h6397, h6412, h7, hc23, hc34, hlam, hphi, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h1, h5072, h6397, h7, hc23, hc45, hlam, hphi, ht34, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6399, h6406, h6410, hc23, hc45, hlam, hphi, ht34, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6406, h6410, hc23, hc45, hlam, hphi, ht34, p6550_1]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [h6412, hlam, p6550_0]
                                                    · have p6550_0 := h6550c.1
                                                      have p6550_1 := h6550c.2.1
                                                      have p6550_2 := h6550c.2.2.1
                                                      have p6550_3 := h6550c.2.2.2
                                                      linarith only [hlam, p6550_0]
                                                  · linarith only [h6549, hlam, p6507_0]
                                                · linarith only [h6548, h7, hlam]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          rcases p6507_3 (m.d 0 3) (by simp) with h6578 | h6578
                                          · linarith only [h4553, h6578, hlam]
                                          · linarith only [h1, h6578, hlam]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          rcases p6507_3 (m.d 0 3) (by simp) with h6581 | h6581
                                          · linarith only [h4553, h6581, hlam]
                                          · linarith only [h4, h6581, hlam]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [h6412, hlam, p6507_0]
                                        · have p6507_0 := h6507c.1
                                          have p6507_1 := h6507c.2.1
                                          have p6507_2 := h6507c.2.2.1
                                          have p6507_3 := h6507c.2.2.2
                                          linarith only [hlam, p6507_0]
                              · linarith only [h0, h6498, hlam]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              rcases p6496_3 (m.d 0 2) (by simp) with h6587 | h6587
                              · rcases p6496_3 (m.d 1 2) (by simp) with h6588 | h6588
                                · linarith only [h0, h6588, hlam]
                                · linarith only [h6397, h6588, hlam]
                              · linarith only [h6587, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              rcases p6496_3 (m.d 0 2) (by simp) with h6592 | h6592
                              · rcases p6496_3 (m.d 1 2) (by simp) with h6593 | h6593
                                · linarith only [h0, h6593, hlam]
                                · linarith only [h6398, h6593, hlam]
                              · linarith only [h6592, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              rcases p6496_3 (m.d 0 2) (by simp) with h6597 | h6597
                              · rcases p6496_3 (m.d 1 2) (by simp) with h6598 | h6598
                                · linarith only [h0, h6598, hlam]
                                · linarith only [h6399, h6598, hlam]
                              · linarith only [h6597, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h0, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              rcases p6496_3 (m.d 0 2) (by simp) with h6604 | h6604
                              · rcases p6496_3 (m.d 1 2) (by simp) with h6605 | h6605
                                · rcases p6496_3 (m.d 2 3) (by simp) with h6606 | h6606
                                  · linarith only [h6606, hlam, p6496_0]
                                  · rcases p6496_3 (m.d 2 4) (by simp) with h6608 | h6608
                                    · linarith only [h6398, h6608, hlam]
                                    · linarith only [h6406, h6608, hlam]
                                · linarith only [h6605, hlam, p6496_0]
                              · linarith only [h4, h6604, hlam]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              rcases p6496_3 (m.d 0 2) (by simp) with h6613 | h6613
                              · rcases p6496_3 (m.d 1 2) (by simp) with h6614 | h6614
                                · rcases p6496_3 (m.d 2 3) (by simp) with h6615 | h6615
                                  · linarith only [h6397, h6615, hlam]
                                  · rcases p6496_3 (m.d 2 4) (by simp) with h6617 | h6617
                                    · linarith only [h6617, hlam, p6496_0]
                                    · rcases p6496_3 (m.d 2 5) (by simp) with h6619 | h6619
                                      · linarith only [h6399, h6619, hlam]
                                      · linarith only [h6410, h6619, hlam]
                                · linarith only [h6614, hlam, p6496_0]
                              · linarith only [h5, h6613, hlam]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              rcases p6496_3 (m.d 0 2) (by simp) with h6624 | h6624
                              · rcases p6496_3 (m.d 1 2) (by simp) with h6625 | h6625
                                · rcases p6496_3 (m.d 2 3) (by simp) with h6626 | h6626
                                  · linarith only [h6397, h6626, hlam]
                                  · rcases p6496_3 (m.d 2 4) (by simp) with h6628 | h6628
                                    · linarith only [h6398, h6628, hlam]
                                    · rcases p6496_3 (m.d 2 5) (by simp) with h6630 | h6630
                                      · linarith only [h6630, hlam, p6496_0]
                                      · rcases h3bigk with h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c | h6632c
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h5072, h6397, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6632_1]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h0, h5072, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6632_1]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h7, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h4553, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h1, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h0, h1, h5072, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6632_1]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h6400, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h6402, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h4, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h6397, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h6406, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h6408, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          rcases p6632_3 (m.d 0 3) (by simp) with h6648 | h6648
                                          · linarith only [h6648, hlam, p6632_0]
                                          · rcases p6632_3 (m.d 1 3) (by simp) with h6650 | h6650
                                            · linarith only [h6400, h6650, hlam]
                                            · rcases p6632_3 (m.d 2 3) (by simp) with h6652 | h6652
                                              · linarith only [h6406, h6652, hlam]
                                              · rcases p6632_3 (m.d 3 4) (by simp) with h6654 | h6654
                                                · rcases p6632_3 (m.d 3 5) (by simp) with h6655 | h6655
                                                  · linarith only [h6412, h6655, hlam]
                                                  · linarith only [h4553, h6655, hlam]
                                                · linarith only [h6654, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          rcases p6632_3 (m.d 0 3) (by simp) with h6659 | h6659
                                          · linarith only [h6659, h7, hlam]
                                          · linarith only [h1, h6659, hlam]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          rcases p6632_3 (m.d 0 3) (by simp) with h6662 | h6662
                                          · linarith only [h6662, h7, hlam]
                                          · linarith only [h4, h6662, hlam]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h4553, hc03, hc34, hlam, hphi, p6632_1]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          rcases p6632_3 (m.d 0 3) (by simp) with h6667 | h6667
                                          · linarith only [h6667, hlam, p6632_0]
                                          · rcases p6632_3 (m.d 1 3) (by simp) with h6669 | h6669
                                            · linarith only [h6402, h6669, hlam]
                                            · rcases p6632_3 (m.d 2 3) (by simp) with h6671 | h6671
                                              · linarith only [h6408, h6671, hlam]
                                              · rcases p6632_3 (m.d 3 4) (by simp) with h6673 | h6673
                                                · rcases p6632_3 (m.d 3 5) (by simp) with h6674 | h6674
                                                  · rcases h5bigk with h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c | h6675c
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [hlam, p6675_0]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h0, h6404, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p6413_1, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h0, h6406, h6410, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h4553, hlam, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h5072, hlam, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h3, hlam, p6675_0]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [hlam, p6675_0]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h3, h6406, h6410, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6402, hlam, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6404, hlam, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6, hlam, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6399, hlam, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [hlam, p6675_0]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6408, hlam, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6410, hlam, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6, h6406, h6410, hc23, hc35, hlam, hphi, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6399, h6406, h6410, hc23, hc35, hlam, hphi, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6406, h6410, hc23, hc35, hlam, hphi, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [hlam, p6675_0]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h2, h5072, h6398, h6406, h6412, hc23, hc34, hlam, hphi, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h2, h5072, h6398, h6406, hc23, hc45, hlam, hphi, ht34, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6399, h6406, h6410, hc23, hc45, hlam, hphi, ht34, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6406, h6410, hc23, hc45, hlam, hphi, ht34, p6675_1]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [h6412, hlam, p6675_0]
                                                    · have p6675_0 := h6675c.1
                                                      have p6675_1 := h6675c.2.1
                                                      have p6675_2 := h6675c.2.2.1
                                                      have p6675_3 := h6675c.2.2.2
                                                      linarith only [hlam, p6675_0]
                                                  · linarith only [h6674, hlam, p6632_0]
                                                · linarith only [h6673, h7, hlam]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          rcases p6632_3 (m.d 0 3) (by simp) with h6703 | h6703
                                          · linarith only [h4553, h6703, hlam]
                                          · linarith only [h1, h6703, hlam]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          rcases p6632_3 (m.d 0 3) (by simp) with h6706 | h6706
                                          · linarith only [h4553, h6706, hlam]
                                          · linarith only [h4, h6706, hlam]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [h6412, hlam, p6632_0]
                                        · have p6632_0 := h6632c.1
                                          have p6632_1 := h6632c.2.1
                                          have p6632_2 := h6632c.2.2.1
                                          have p6632_3 := h6632c.2.2.2
                                          linarith only [hlam, p6632_0]
                                · linarith only [h6625, hlam, p6496_0]
                              · linarith only [h6, h6624, hlam]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h4, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h6397, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h6406, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h6408, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h5, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h6398, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h0, h2, h5072, h6398, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6496_1]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h6410, hlam, p6496_1]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h6, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h6399, hlam, p6496_0]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h0, h3, h6399, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6413_1, p6496_1]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [h0, h3, h6399, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6413_1, p6496_1]
                            · have p6496_0 := h6496c.1
                              have p6496_1 := h6496c.2.1
                              have p6496_2 := h6496c.2.2.1
                              have p6496_3 := h6496c.2.2.2
                              linarith only [hlam, p6496_0]
                    · linarith only [h6, h6489, hlam]
                  · linarith only [h3, h6488, hlam]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h1, hlam, p6413_1]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h4, hlam, p6413_1]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [hlam, p6413_0]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h7, hlam, p6413_1]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h4553, hlam, p6413_1]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h2, hlam, p6413_0]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h5, hlam, p6413_0]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h1, h5072, h6397, h6412, hc23, hc34, hlam, hphi, p6413_1]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [hlam, p6413_0]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h5072, hlam, p6413_0]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h3, hlam, p6413_0]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h6, hlam, p6413_1]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h1, h5072, h6397, h6412, hc23, hc34, hlam, hphi, p6413_1]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [h1, h5072, h6397, h6412, h7, hc23, hc34, hlam, hphi, p6413_1]
                · have p6413_0 := h6413c.1
                  have p6413_1 := h6413c.2.1
                  have p6413_2 := h6413c.2.2.1
                  have p6413_3 := h6413c.2.2.2
                  linarith only [hlam, p6413_0]
              · rcases h0bigk with h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c | h6745c
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [hlam, p6745_0]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  rcases p6745_3 (m.d 0 1) (by simp) with h6747 | h6747
                  · rcases p6745_3 (m.d 0 2) (by simp) with h6748 | h6748
                    · linarith only [h0, h6748, hlam]
                    · rcases p6745_3 (m.d 0 3) (by simp) with h6750 | h6750
                      · linarith only [h1, h6750, hlam]
                      · rcases p6745_3 (m.d 0 4) (by simp) with h6752 | h6752
                        · linarith only [h2, h6752, hlam]
                        · rcases p6745_3 (m.d 0 5) (by simp) with h6754 | h6754
                          · linarith only [h3, h6754, hlam]
                          · rcases h2bigk with h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c | h6756c
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h6406, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [hc01, hc25, hlam, hphi, ht0b, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h0, hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h0, h6406, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h4, hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h6397, hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h6406, hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h6408, hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h5, hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h6398, hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h6410, hlam, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h6, hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h6399, hlam, p6756_0]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [h0, h6399, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6745_1, p6756_1]
                            · have p6756_0 := h6756c.1
                              have p6756_1 := h6756c.2.1
                              have p6756_2 := h6756c.2.2.1
                              have p6756_3 := h6756c.2.2.2
                              linarith only [hlam, p6756_0]
                  · linarith only [h0, h6747, hlam]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  rcases p6745_3 (m.d 0 1) (by simp) with h6783 | h6783
                  · rcases p6745_3 (m.d 0 2) (by simp) with h6784 | h6784
                    · linarith only [h0, h6784, hlam]
                    · linarith only [h4, h6784, hlam]
                  · linarith only [h1, h6783, hlam]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  rcases p6745_3 (m.d 0 1) (by simp) with h6788 | h6788
                  · rcases p6745_3 (m.d 0 2) (by simp) with h6789 | h6789
                    · linarith only [h0, h6789, hlam]
                    · linarith only [h5, h6789, hlam]
                  · linarith only [h2, h6788, hlam]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  rcases p6745_3 (m.d 0 1) (by simp) with h6793 | h6793
                  · rcases p6745_3 (m.d 0 2) (by simp) with h6794 | h6794
                    · linarith only [h0, h6794, hlam]
                    · linarith only [h6, h6794, hlam]
                  · linarith only [h3, h6793, hlam]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h0, hlam, p6745_0]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [hlam, p6745_0]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  rcases p6745_3 (m.d 0 1) (by simp) with h6800 | h6800
                  · rcases p6745_3 (m.d 0 2) (by simp) with h6801 | h6801
                    · rcases p6745_3 (m.d 0 3) (by simp) with h6802 | h6802
                      · linarith only [h4, h6802, hlam]
                      · rcases p6745_3 (m.d 0 4) (by simp) with h6804 | h6804
                        · linarith only [h5, h6804, hlam]
                        · linarith only [h6804, h7, hlam]
                    · linarith only [h4, h6801, hlam]
                  · linarith only [h1, h6800, hlam]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  rcases p6745_3 (m.d 0 1) (by simp) with h6809 | h6809
                  · rcases p6745_3 (m.d 0 2) (by simp) with h6810 | h6810
                    · rcases p6745_3 (m.d 0 3) (by simp) with h6811 | h6811
                      · linarith only [h4, h6811, hlam]
                      · rcases p6745_3 (m.d 0 4) (by simp) with h6813 | h6813
                        · linarith only [h5, h6813, hlam]
                        · rcases p6745_3 (m.d 0 5) (by simp) with h6815 | h6815
                          · linarith only [h6, h6815, hlam]
                          · linarith only [h5072, h6815, hlam]
                    · linarith only [h5, h6810, hlam]
                  · linarith only [h2, h6809, hlam]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  rcases p6745_3 (m.d 0 1) (by simp) with h6820 | h6820
                  · rcases p6745_3 (m.d 0 2) (by simp) with h6821 | h6821
                    · rcases p6745_3 (m.d 0 3) (by simp) with h6822 | h6822
                      · linarith only [h4, h6822, hlam]
                      · rcases p6745_3 (m.d 0 4) (by simp) with h6824 | h6824
                        · linarith only [h5, h6824, hlam]
                        · rcases p6745_3 (m.d 0 5) (by simp) with h6826 | h6826
                          · linarith only [h6, h6826, hlam]
                          · rcases h2bigk with h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c | h6828c
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              rcases p6828_3 (m.d 0 2) (by simp) with h6830 | h6830
                              · rcases p6828_3 (m.d 1 2) (by simp) with h6831 | h6831
                                · linarith only [h0, h6831, hlam]
                                · rcases p6828_3 (m.d 2 3) (by simp) with h6833 | h6833
                                  · linarith only [h4, h6833, hlam]
                                  · rcases p6828_3 (m.d 2 4) (by simp) with h6835 | h6835
                                    · linarith only [h5, h6835, hlam]
                                    · rcases p6828_3 (m.d 2 5) (by simp) with h6837 | h6837
                                      · linarith only [h6, h6837, hlam]
                                      · rcases h3bigk with h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c | h6839c
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6397, h7, hc23, hc34, hlam, hphi, p6839_1]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h7, hc23, hc34, hlam, hphi, p6839_1]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h7, hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h4553, hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h1, hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h1, h7, hc23, hc34, hlam, hphi, p6839_1]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6400, hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6402, hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h4, hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6397, hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6406, hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6408, hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6412, hc03, hc45, hlam, hphi, ht34, p6839_1]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6397, h6412, hc23, hc45, hlam, hphi, ht34, p6839_1]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6412, hc23, hc45, hlam, hphi, ht34, p6839_1]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [hlam, p6839_0]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h6412, hlam, p6839_1]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          rcases p6839_3 (m.d 0 3) (by simp) with h6860 | h6860
                                          · linarith only [h6860, hlam, p6839_0]
                                          · rcases p6839_3 (m.d 1 3) (by simp) with h6862 | h6862
                                            · linarith only [h6402, h6862, hlam]
                                            · rcases p6839_3 (m.d 2 3) (by simp) with h6864 | h6864
                                              · linarith only [h6408, h6864, hlam]
                                              · rcases p6839_3 (m.d 3 4) (by simp) with h6866 | h6866
                                                · linarith only [h6412, h6866, hlam]
                                                · linarith only [h6866, h7, hlam]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          rcases p6839_3 (m.d 0 3) (by simp) with h6869 | h6869
                                          · linarith only [h4553, h6869, hlam]
                                          · linarith only [h1, h6869, hlam]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          rcases p6839_3 (m.d 0 3) (by simp) with h6872 | h6872
                                          · linarith only [h4553, h6872, hlam]
                                          · linarith only [h4, h6872, hlam]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [h1, h6397, h6412, h7, hc23, hc45, hlam, hphi, ht34, p6839_1]
                                        · have p6839_0 := h6839c.1
                                          have p6839_1 := h6839c.2.1
                                          have p6839_2 := h6839c.2.2.1
                                          have p6839_3 := h6839c.2.2.2
                                          linarith only [hlam, p6839_0]
                              · linarith only [h0, h6830, hlam]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              rcases p6828_3 (m.d 0 2) (by simp) with h6878 | h6878
                              · rcases p6828_3 (m.d 1 2) (by simp) with h6879 | h6879
                                · linarith only [h0, h6879, hlam]
                                · linarith only [h6397, h6879, hlam]
                              · linarith only [h6878, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              rcases p6828_3 (m.d 0 2) (by simp) with h6883 | h6883
                              · rcases p6828_3 (m.d 1 2) (by simp) with h6884 | h6884
                                · linarith only [h0, h6884, hlam]
                                · linarith only [h6398, h6884, hlam]
                              · linarith only [h6883, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              rcases p6828_3 (m.d 0 2) (by simp) with h6888 | h6888
                              · rcases p6828_3 (m.d 1 2) (by simp) with h6889 | h6889
                                · linarith only [h0, h6889, hlam]
                                · linarith only [h6399, h6889, hlam]
                              · linarith only [h6888, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h0, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              rcases p6828_3 (m.d 0 2) (by simp) with h6895 | h6895
                              · rcases p6828_3 (m.d 1 2) (by simp) with h6896 | h6896
                                · rcases p6828_3 (m.d 2 3) (by simp) with h6897 | h6897
                                  · linarith only [h6897, hlam, p6828_0]
                                  · rcases p6828_3 (m.d 2 4) (by simp) with h6899 | h6899
                                    · linarith only [h6398, h6899, hlam]
                                    · linarith only [h6406, h6899, hlam]
                                · linarith only [h6896, hlam, p6828_0]
                              · linarith only [h4, h6895, hlam]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              rcases p6828_3 (m.d 0 2) (by simp) with h6904 | h6904
                              · rcases p6828_3 (m.d 1 2) (by simp) with h6905 | h6905
                                · rcases p6828_3 (m.d 2 3) (by simp) with h6906 | h6906
                                  · linarith only [h6397, h6906, hlam]
                                  · rcases p6828_3 (m.d 2 4) (by simp) with h6908 | h6908
                                    · linarith only [h6908, hlam, p6828_0]
                                    · rcases p6828_3 (m.d 2 5) (by simp) with h6910 | h6910
                                      · linarith only [h6399, h6910, hlam]
                                      · linarith only [h6410, h6910, hlam]
                                · linarith only [h6905, hlam, p6828_0]
                              · linarith only [h5, h6904, hlam]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              rcases p6828_3 (m.d 0 2) (by simp) with h6915 | h6915
                              · rcases p6828_3 (m.d 1 2) (by simp) with h6916 | h6916
                                · rcases p6828_3 (m.d 2 3) (by simp) with h6917 | h6917
                                  · linarith only [h6397, h6917, hlam]
                                  · rcases p6828_3 (m.d 2 4) (by simp) with h6919 | h6919
                                    · linarith only [h6398, h6919, hlam]
                                    · rcases p6828_3 (m.d 2 5) (by simp) with h6921 | h6921
                                      · linarith only [h6921, hlam, p6828_0]
                                      · rcases h3bigk with h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c | h6923c
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6397, h7, hc23, hc34, hlam, hphi, p6923_1]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h7, hc23, hc34, hlam, hphi, p6923_1]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h7, hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h4553, hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h1, hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h1, h7, hc23, hc34, hlam, hphi, p6923_1]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6400, hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6402, hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h4, hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6397, hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6406, hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6408, hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6412, hc03, hc45, hlam, hphi, ht34, p6923_1]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6397, h6412, hc23, hc45, hlam, hphi, ht34, p6923_1]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6412, hc23, hc45, hlam, hphi, ht34, p6923_1]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [hlam, p6923_0]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h6412, hlam, p6923_1]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          rcases p6923_3 (m.d 0 3) (by simp) with h6944 | h6944
                                          · linarith only [h6944, hlam, p6923_0]
                                          · rcases p6923_3 (m.d 1 3) (by simp) with h6946 | h6946
                                            · linarith only [h6402, h6946, hlam]
                                            · rcases p6923_3 (m.d 2 3) (by simp) with h6948 | h6948
                                              · linarith only [h6408, h6948, hlam]
                                              · rcases p6923_3 (m.d 3 4) (by simp) with h6950 | h6950
                                                · linarith only [h6412, h6950, hlam]
                                                · linarith only [h6950, h7, hlam]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          rcases p6923_3 (m.d 0 3) (by simp) with h6953 | h6953
                                          · linarith only [h4553, h6953, hlam]
                                          · linarith only [h1, h6953, hlam]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          rcases p6923_3 (m.d 0 3) (by simp) with h6956 | h6956
                                          · linarith only [h4553, h6956, hlam]
                                          · linarith only [h4, h6956, hlam]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [h1, h6397, h6412, h7, hc23, hc45, hlam, hphi, ht34, p6923_1]
                                        · have p6923_0 := h6923c.1
                                          have p6923_1 := h6923c.2.1
                                          have p6923_2 := h6923c.2.2.1
                                          have p6923_3 := h6923c.2.2.2
                                          linarith only [hlam, p6923_0]
                                · linarith only [h6916, hlam, p6828_0]
                              · linarith only [h6, h6915, hlam]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h4, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h6397, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h6406, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h6408, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h5, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h6398, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h5, h5072, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6745_1, p6828_1]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h6410, hlam, p6828_1]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h6, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h6399, hlam, p6828_0]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h0, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6745_1, p6828_1]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [h0, h3, h6399, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6745_1, p6828_1]
                            · have p6828_0 := h6828c.1
                              have p6828_1 := h6828c.2.1
                              have p6828_2 := h6828c.2.2.1
                              have p6828_3 := h6828c.2.2.2
                              linarith only [hlam, p6828_0]
                    · linarith only [h6, h6821, hlam]
                  · linarith only [h3, h6820, hlam]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h1, hlam, p6745_1]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h4, hlam, p6745_1]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [hlam, p6745_0]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h7, hlam, p6745_1]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h4553, hlam, p6745_1]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h2, hlam, p6745_0]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h5, hlam, p6745_0]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h1, h5072, h6397, hc23, hc45, hlam, hphi, ht34, p6745_1]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [hlam, p6745_0]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h5072, hlam, p6745_0]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h3, hlam, p6745_0]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [h6, hlam, p6745_1]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  rcases p6745_3 (m.d 0 1) (by simp) with h6992 | h6992
                  · rcases p6745_3 (m.d 0 2) (by simp) with h6993 | h6993
                    · rcases p6745_3 (m.d 0 3) (by simp) with h6994 | h6994
                      · linarith only [h4553, h6994, hlam]
                      · rcases p6745_3 (m.d 0 4) (by simp) with h6996 | h6996
                        · linarith only [h5072, h6996, hlam]
                        · linarith only [h6996, h7, hlam]
                    · linarith only [h4, h6993, hlam]
                  · linarith only [h1, h6992, hlam]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  rcases p6745_3 (m.d 0 1) (by simp) with h7001 | h7001
                  · rcases p6745_3 (m.d 0 2) (by simp) with h7002 | h7002
                    · rcases p6745_3 (m.d 0 3) (by simp) with h7003 | h7003
                      · linarith only [h4553, h7003, hlam]
                      · rcases p6745_3 (m.d 0 4) (by simp) with h7005 | h7005
                        · linarith only [h5072, h7005, hlam]
                        · rcases p6745_3 (m.d 0 5) (by simp) with h7007 | h7007
                          · rcases h2bigk with h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c | h7008c
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              rcases p7008_3 (m.d 0 2) (by simp) with h7010 | h7010
                              · rcases p7008_3 (m.d 1 2) (by simp) with h7011 | h7011
                                · linarith only [h0, h7011, hlam]
                                · rcases p7008_3 (m.d 2 3) (by simp) with h7013 | h7013
                                  · linarith only [h4, h7013, hlam]
                                  · rcases p7008_3 (m.d 2 4) (by simp) with h7015 | h7015
                                    · linarith only [h5, h7015, hlam]
                                    · rcases p7008_3 (m.d 2 5) (by simp) with h7017 | h7017
                                      · linarith only [h6, h7017, hlam]
                                      · rcases h3bigk with h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6397, h6412, h7, hc23, hc45, hlam, hphi, ht34, p7019_1]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6412, h7, hc23, hc45, hlam, hphi, ht34, p7019_1]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h7, hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h4553, hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h1, hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h1, h6412, h7, hc23, hc45, hlam, hphi, ht34, p7019_1]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6400, hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6402, hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h4, hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6397, hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6406, hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6408, hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6412, hc03, hc45, hlam, hphi, ht34, p7019_1]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6412, hc13, hc45, hlam, hphi, ht34, p7019_1]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6412, hc23, hc45, hlam, hphi, ht34, p7019_1]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [hlam, p7019_0]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6412, hlam, p7019_1]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          rcases p7019_3 (m.d 0 3) (by simp) with h7040 | h7040
                                          · linarith only [h7040, hlam, p7019_0]
                                          · rcases p7019_3 (m.d 1 3) (by simp) with h7042 | h7042
                                            · linarith only [h6402, h7042, hlam]
                                            · rcases p7019_3 (m.d 2 3) (by simp) with h7044 | h7044
                                              · linarith only [h6408, h7044, hlam]
                                              · rcases p7019_3 (m.d 3 4) (by simp) with h7046 | h7046
                                                · linarith only [h6412, h7046, hlam]
                                                · linarith only [h7, h7046, hlam]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          rcases p7019_3 (m.d 0 3) (by simp) with h7049 | h7049
                                          · linarith only [h4553, h7049, hlam]
                                          · linarith only [h1, h7049, hlam]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          rcases p7019_3 (m.d 0 3) (by simp) with h7052 | h7052
                                          · linarith only [h4553, h7052, hlam]
                                          · linarith only [h4, h7052, hlam]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [h6412, h7, hc03, hc45, hlam, hphi, ht34, p7019_1]
                                        · have p7019_0 := h7019c.1
                                          have p7019_1 := h7019c.2.1
                                          have p7019_2 := h7019c.2.2.1
                                          have p7019_3 := h7019c.2.2.2
                                          linarith only [hlam, p7019_0]
                              · linarith only [h0, h7010, hlam]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              rcases p7008_3 (m.d 0 2) (by simp) with h7058 | h7058
                              · rcases p7008_3 (m.d 1 2) (by simp) with h7059 | h7059
                                · linarith only [h0, h7059, hlam]
                                · linarith only [h6397, h7059, hlam]
                              · linarith only [h7058, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              rcases p7008_3 (m.d 0 2) (by simp) with h7063 | h7063
                              · rcases p7008_3 (m.d 1 2) (by simp) with h7064 | h7064
                                · linarith only [h0, h7064, hlam]
                                · linarith only [h6398, h7064, hlam]
                              · linarith only [h7063, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              rcases p7008_3 (m.d 0 2) (by simp) with h7068 | h7068
                              · rcases p7008_3 (m.d 1 2) (by simp) with h7069 | h7069
                                · linarith only [h0, h7069, hlam]
                                · linarith only [h6399, h7069, hlam]
                              · linarith only [h7068, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h0, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              rcases p7008_3 (m.d 0 2) (by simp) with h7075 | h7075
                              · rcases p7008_3 (m.d 1 2) (by simp) with h7076 | h7076
                                · rcases p7008_3 (m.d 2 3) (by simp) with h7077 | h7077
                                  · linarith only [h7077, hlam, p7008_0]
                                  · rcases p7008_3 (m.d 2 4) (by simp) with h7079 | h7079
                                    · linarith only [h6398, h7079, hlam]
                                    · linarith only [h6406, h7079, hlam]
                                · linarith only [h7076, hlam, p7008_0]
                              · linarith only [h4, h7075, hlam]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              rcases p7008_3 (m.d 0 2) (by simp) with h7084 | h7084
                              · rcases p7008_3 (m.d 1 2) (by simp) with h7085 | h7085
                                · rcases p7008_3 (m.d 2 3) (by simp) with h7086 | h7086
                                  · linarith only [h6397, h7086, hlam]
                                  · rcases p7008_3 (m.d 2 4) (by simp) with h7088 | h7088
                                    · linarith only [h7088, hlam, p7008_0]
                                    · rcases p7008_3 (m.d 2 5) (by simp) with h7090 | h7090
                                      · linarith only [h6399, h7090, hlam]
                                      · linarith only [h6410, h7090, hlam]
                                · linarith only [h7085, hlam, p7008_0]
                              · linarith only [h5, h7084, hlam]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              rcases p7008_3 (m.d 0 2) (by simp) with h7095 | h7095
                              · rcases p7008_3 (m.d 1 2) (by simp) with h7096 | h7096
                                · rcases p7008_3 (m.d 2 3) (by simp) with h7097 | h7097
                                  · linarith only [h6397, h7097, hlam]
                                  · rcases p7008_3 (m.d 2 4) (by simp) with h7099 | h7099
                                    · linarith only [h6398, h7099, hlam]
                                    · rcases p7008_3 (m.d 2 5) (by simp) with h7101 | h7101
                                      · linarith only [h7101, hlam, p7008_0]
                                      · rcases h3bigk with h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c | h7103c
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6397, h7, hc23, hc34, hlam, hphi, p7103_1]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h7, hc23, hc34, hlam, hphi, p7103_1]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h7, hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h4553, hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h1, hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h1, h7, hc23, hc34, hlam, hphi, p7103_1]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6400, hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6402, hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h4, hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6397, hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6406, hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6408, hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6412, hc03, hc45, hlam, hphi, ht34, p7103_1]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6397, h6412, hc23, hc45, hlam, hphi, ht34, p7103_1]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6412, hc23, hc45, hlam, hphi, ht34, p7103_1]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [hlam, p7103_0]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h6412, hlam, p7103_1]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          rcases p7103_3 (m.d 0 3) (by simp) with h7124 | h7124
                                          · linarith only [h7124, hlam, p7103_0]
                                          · rcases p7103_3 (m.d 1 3) (by simp) with h7126 | h7126
                                            · linarith only [h6402, h7126, hlam]
                                            · rcases p7103_3 (m.d 2 3) (by simp) with h7128 | h7128
                                              · linarith only [h6408, h7128, hlam]
                                              · rcases p7103_3 (m.d 3 4) (by simp) with h7130 | h7130
                                                · linarith only [h6412, h7130, hlam]
                                                · linarith only [h7, h7130, hlam]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          rcases p7103_3 (m.d 0 3) (by simp) with h7133 | h7133
                                          · linarith only [h4553, h7133, hlam]
                                          · linarith only [h1, h7133, hlam]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          rcases p7103_3 (m.d 0 3) (by simp) with h7136 | h7136
                                          · linarith only [h4553, h7136, hlam]
                                          · linarith only [h4, h7136, hlam]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [h1, h6397, h6412, h7, hc23, hc45, hlam, hphi, ht34, p7103_1]
                                        · have p7103_0 := h7103c.1
                                          have p7103_1 := h7103c.2.1
                                          have p7103_2 := h7103c.2.2.1
                                          have p7103_3 := h7103c.2.2.2
                                          linarith only [hlam, p7103_0]
                                · linarith only [h7096, hlam, p7008_0]
                              · linarith only [h6, h7095, hlam]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h4, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h6397, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h6406, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h6408, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h5, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h6398, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h4553, h5, h6412, hc23, hc45, hlam, hphi, ht34, p6745_1, p7008_1]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h6410, hlam, p7008_1]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h6, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h6399, hlam, p7008_0]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h0, h6399, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7008_1]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [h0, h6399, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p7008_1]
                            · have p7008_0 := h7008c.1
                              have p7008_1 := h7008c.2.1
                              have p7008_2 := h7008c.2.2.1
                              have p7008_3 := h7008c.2.2.2
                              linarith only [hlam, p7008_0]
                          · linarith only [h5072, h7007, hlam]
                    · linarith only [h5, h7002, hlam]
                  · linarith only [h2, h7001, hlam]
                · have p6745_0 := h6745c.1
                  have p6745_1 := h6745c.2.1
                  have p6745_2 := h6745c.2.2.1
                  have p6745_3 := h6745c.2.2.2
                  linarith only [hlam, p6745_0]

end R2N4
