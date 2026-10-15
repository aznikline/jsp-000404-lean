import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 28790000 in
set_option maxHeartbeats 28790000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h13364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h13365 | h13365
  · rcases m.htr 0 2 3 (by decide) (by decide) with h13366 | h13366
    · linarith only [h0, h1, h13366, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h13368 | h13368
      · rcases m.htr 0 2 5 (by decide) (by decide) with h13369 | h13369
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13370 | h13370
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13371 | h13371
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13372 | h13372
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13373 | h13373
                · linarith only [h0, h1, h13366, h13368, h13373, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13375 | h13375
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13376 | h13376
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13377 | h13377
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13378 | h13378
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13379 | h13379
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13380 | h13380
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13381 | h13381
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13382 | h13382
                                · linarith only [h0, h1, h13373, h13375, h13382, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                                · linarith only [h0, h1, h13373, h13375, h13379, h13382, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h1, h13373, h13381, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h13373, h13380, hc12, hc34, hlam, hphi, ht23]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13387 | h13387
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13388 | h13388
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13389 | h13389
                                · linarith only [h13375, h13379, h13389, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13391 | h13391
                                  · linarith only [h13375, h13379, h13387, h13391, hlam]
                                  · rcases h0bigk with h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c | h13393c
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h1, h13373, hc02, hc23, hlam, hphi, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h1, hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h1, h13372, h13373, h13375, h13379, h13387, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h1, h13372, h13373, h13375, h13379, h13387, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h0, hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h13366, hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h13372, h13375, h13379, h13387, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h0, h1, h13372, h13373, h13375, h13379, h13387, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h0, h1, h13373, hc12, hc23, hlam, hphi, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h1, h13368, h13372, h13373, h13375, h13379, h13387, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h1, h13372, h13373, h13375, h13379, h13387, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      rcases p13393_3 (m.d 0 1) (by simp) with h13408 | h13408
                                      · linarith only [h1, h13408, hlam]
                                      · linarith only [h13365, h13408, hlam]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h13364, hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h13368, hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h13370, hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h0, h1, h13368, h13372, h13373, h13375, h13379, h13387, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h13365, hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h13369, hlam, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h13371, hlam, p13393_0]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [h13372, hlam, p13393_1]
                                    · have p13393_0 := h13393c.1
                                      have p13393_1 := h13393c.2.1
                                      have p13393_2 := h13393c.2.2.1
                                      have p13393_3 := h13393c.2.2.2
                                      linarith only [hlam, p13393_0]
                              · linarith only [h0, h1, h13373, h13388, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h13368, h13372, h13373, h13375, h13379, h13387, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h13378, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h13377, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h1, h13369, h13375, h13376, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h13368, h13373, h13375, hc12, hc23, hlam, hphi]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13427 | h13427
                · linarith only [h0, h1, h13366, h13427, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13429 | h13429
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13430 | h13430
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13431 | h13431
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13432 | h13432
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13433 | h13433
                          · linarith only [h13364, h13372, h13433, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13435 | h13435
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13436 | h13436
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13437 | h13437
                                · linarith only [h0, h1, h13372, h13427, h13429, h13437, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13439 | h13439
                                  · linarith only [h13370, h13372, h13439, hlam]
                                  · rcases h0bigk with h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c | h13441c
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h1, h13427, hc02, hc23, hlam, hphi, p13441_1]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h1, hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      rcases p13441_3 (m.d 0 1) (by simp) with h13445 | h13445
                                      · rcases p13441_3 (m.d 0 2) (by simp) with h13446 | h13446
                                        · linarith only [h0, h13446, hlam]
                                        · linarith only [h13368, h13446, hlam]
                                      · linarith only [h13364, h13445, hlam]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      rcases p13441_3 (m.d 0 1) (by simp) with h13450 | h13450
                                      · rcases p13441_3 (m.d 0 2) (by simp) with h13451 | h13451
                                        · linarith only [h0, h13451, hlam]
                                        · linarith only [h13369, h13451, hlam]
                                      · linarith only [h13365, h13450, hlam]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h0, hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h13366, hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      rcases p13441_3 (m.d 0 1) (by simp) with h13458 | h13458
                                      · rcases p13441_3 (m.d 0 2) (by simp) with h13459 | h13459
                                        · rcases p13441_3 (m.d 0 3) (by simp) with h13460 | h13460
                                          · rcases p13441_3 (m.d 0 4) (by simp) with h13461 | h13461
                                            · linarith only [h13368, h13461, hlam]
                                            · rcases p13441_3 (m.d 0 5) (by simp) with h13463 | h13463
                                              · linarith only [h13369, h13463, hlam]
                                              · linarith only [h13372, h13463, hlam]
                                          · linarith only [h13370, h13460, hlam]
                                        · linarith only [h13368, h13459, hlam]
                                      · linarith only [h13364, h13458, hlam]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      rcases p13441_3 (m.d 0 1) (by simp) with h13469 | h13469
                                      · rcases p13441_3 (m.d 0 2) (by simp) with h13470 | h13470
                                        · rcases p13441_3 (m.d 0 3) (by simp) with h13471 | h13471
                                          · rcases p13441_3 (m.d 0 4) (by simp) with h13472 | h13472
                                            · linarith only [h13368, h13472, hlam]
                                            · rcases p13441_3 (m.d 0 5) (by simp) with h13474 | h13474
                                              · linarith only [h13369, h13474, hlam]
                                              · rcases h2bigk with h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c | h13476c
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h0, h1, h13427, hc12, hc23, hlam, hphi, p13476_1]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13366, hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  rcases p13476_3 (m.d 0 2) (by simp) with h13480 | h13480
                                                  · rcases p13476_3 (m.d 1 2) (by simp) with h13481 | h13481
                                                    · linarith only [h0, h13481, hlam]
                                                    · linarith only [h13429, h13481, hlam]
                                                  · linarith only [h13480, hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  rcases p13476_3 (m.d 0 2) (by simp) with h13485 | h13485
                                                  · rcases p13476_3 (m.d 1 2) (by simp) with h13486 | h13486
                                                    · linarith only [h0, h13486, hlam]
                                                    · linarith only [h13430, h13486, hlam]
                                                  · linarith only [h13485, hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h0, hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13427, hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h0, h1, h13427, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13476_1]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h0, h1, h13427, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p13476_1]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13372, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13441_1, p13476_1]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  rcases p13476_3 (m.d 0 2) (by simp) with h13496 | h13496
                                                  · linarith only [h13366, h13496, hlam]
                                                  · linarith only [h0, h13496, hlam]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h0, h1, h13364, h13372, h13427, h13429, hlam, p13441_1, p13476_2]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h0, h1, h13369, h13427, hlam, p13441_1, p13476_2]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13368, hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13429, hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13435, hlam, p13476_1]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13437, hlam, p13476_1]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13369, hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13430, hlam, p13476_0]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h13436, hlam, p13476_1]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [h0, h13365, h13430, h13435, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13441_1, p13476_1]
                                                · have p13476_0 := h13476c.1
                                                  have p13476_1 := h13476c.2.1
                                                  have p13476_2 := h13476c.2.2.1
                                                  have p13476_3 := h13476c.2.2.2
                                                  linarith only [hlam, p13476_0]
                                          · linarith only [h13371, h13471, hlam]
                                        · linarith only [h13369, h13470, hlam]
                                      · linarith only [h13365, h13469, hlam]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h0, h1, h13427, hc12, hc23, hlam, hphi, p13441_1]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      rcases p13441_3 (m.d 0 1) (by simp) with h13516 | h13516
                                      · linarith only [h1, h13516, hlam]
                                      · linarith only [h0, h13516, hlam]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      rcases p13441_3 (m.d 0 1) (by simp) with h13520 | h13520
                                      · linarith only [h1, h13520, hlam]
                                      · linarith only [h13364, h13520, hlam]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      rcases p13441_3 (m.d 0 1) (by simp) with h13523 | h13523
                                      · linarith only [h1, h13523, hlam]
                                      · linarith only [h13365, h13523, hlam]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h13364, hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h13368, hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h13370, hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h13372, hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h13365, hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h13369, hlam, p13441_1]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [h13371, hlam, p13441_0]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      rcases p13441_3 (m.d 0 1) (by simp) with h13534 | h13534
                                      · rcases p13441_3 (m.d 0 2) (by simp) with h13535 | h13535
                                        · rcases p13441_3 (m.d 0 3) (by simp) with h13536 | h13536
                                          · rcases p13441_3 (m.d 0 4) (by simp) with h13537 | h13537
                                            · linarith only [h13372, h13537, hlam]
                                            · rcases p13441_3 (m.d 0 5) (by simp) with h13539 | h13539
                                              · rcases h2bigk with h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c | h13540c
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h0, h1, h13427, h13430, h13436, h13439, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13540_1]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13366, hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  rcases p13540_3 (m.d 0 2) (by simp) with h13544 | h13544
                                                  · rcases p13540_3 (m.d 1 2) (by simp) with h13545 | h13545
                                                    · linarith only [h0, h13545, hlam]
                                                    · linarith only [h13429, h13545, hlam]
                                                  · linarith only [h13544, hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  rcases p13540_3 (m.d 0 2) (by simp) with h13549 | h13549
                                                  · rcases p13540_3 (m.d 1 2) (by simp) with h13550 | h13550
                                                    · linarith only [h0, h13550, hlam]
                                                    · linarith only [h13430, h13550, hlam]
                                                  · linarith only [h13549, hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h0, hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13427, hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h0, h1, h13427, h13435, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13540_1]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h0, h1, h13427, h13436, h13439, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13540_1]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13369, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13441_1, p13540_1]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  rcases p13540_3 (m.d 0 2) (by simp) with h13560 | h13560
                                                  · linarith only [h13366, h13560, hlam]
                                                  · linarith only [h0, h13560, hlam]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h0, h1, h13364, h13369, h13427, h13429, hlam, p13441_1, p13540_2]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h0, h1, h13427, h13430, hlam, p13540_2]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13368, hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13429, hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13435, hlam, p13540_1]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13437, hlam, p13540_1]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13369, hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13430, hlam, p13540_0]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h13436, hlam, p13540_1]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [h0, h13430, h13435, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p13540_1]
                                                · have p13540_0 := h13540c.1
                                                  have p13540_1 := h13540c.2.1
                                                  have p13540_2 := h13540c.2.2.1
                                                  have p13540_3 := h13540c.2.2.2
                                                  linarith only [hlam, p13540_0]
                                              · linarith only [h13372, h13539, hlam]
                                          · linarith only [h13370, h13536, hlam]
                                        · linarith only [h13368, h13535, hlam]
                                      · linarith only [h13364, h13534, hlam]
                                    · have p13441_0 := h13441c.1
                                      have p13441_1 := h13441c.2.1
                                      have p13441_2 := h13441c.2.2.1
                                      have p13441_3 := h13441c.2.2.2
                                      linarith only [hlam, p13441_0]
                              · linarith only [h0, h1, h13427, h13436, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h13427, h13429, h13435, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h0, h1, h13429, h13432, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h13429, h13431, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h13369, h13429, h13430, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h0, h1, h13368, h13427, h13429, hc12, hc23, hlam, hphi]
            · linarith only [h0, h1, h13369, h13371, hlam]
          · linarith only [h1, h13364, h13370, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13589 | h13589
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13590 | h13590
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13591 | h13591
              · linarith only [h13368, h13369, h13591, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13593 | h13593
                · linarith only [h0, h1, h13366, h13593, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13595 | h13595
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13596 | h13596
                    · linarith only [h0, h13369, h13596, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13598 | h13598
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13599 | h13599
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13600 | h13600
                          · linarith only [h13364, h13591, h13600, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13602 | h13602
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13603 | h13603
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13604 | h13604
                                · linarith only [h0, h13364, h13369, h13591, h13595, h13604, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13606 | h13606
                                  · linarith only [h0, h1, h13364, h13369, h13593, h13595, h13602, h13604, h13606, hc12, hc23, hlam, hphi]
                                  · rcases h0bigk with h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c | h13608c
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h0, h1, h13593, h13595, h13602, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13608_1]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h1, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      rcases p13608_3 (m.d 0 1) (by simp) with h13612 | h13612
                                      · rcases p13608_3 (m.d 0 2) (by simp) with h13613 | h13613
                                        · linarith only [h0, h13613, hlam]
                                        · linarith only [h13368, h13613, hlam]
                                      · linarith only [h13364, h13612, hlam]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h0, h1, h13369, h13593, h13595, h13602, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13608_1]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h0, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h13366, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h13364, h13369, h13604, hc14, hc45, hlam, hphi, p13608_1]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h13369, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h0, h13595, h13602, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p13608_1]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      rcases p13608_3 (m.d 0 1) (by simp) with h13624 | h13624
                                      · linarith only [h1, h13624, hlam]
                                      · linarith only [h0, h13624, hlam]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      rcases p13608_3 (m.d 0 1) (by simp) with h13628 | h13628
                                      · linarith only [h1, h13628, hlam]
                                      · linarith only [h13364, h13628, hlam]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      rcases p13608_3 (m.d 0 1) (by simp) with h13631 | h13631
                                      · linarith only [h1, h13631, hlam]
                                      · linarith only [h13365, h13631, hlam]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h13364, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h13368, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h13589, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h13591, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h13365, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h0, h1, h13365, h13593, h13595, h13602, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p13608_1]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [h13590, hlam, p13608_0]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      rcases p13608_3 (m.d 0 1) (by simp) with h13642 | h13642
                                      · rcases p13608_3 (m.d 0 2) (by simp) with h13643 | h13643
                                        · linarith only [h13369, h13643, hlam]
                                        · linarith only [h13368, h13643, hlam]
                                      · linarith only [h13364, h13642, hlam]
                                    · have p13608_0 := h13608c.1
                                      have p13608_1 := h13608c.2.1
                                      have p13608_2 := h13608c.2.2.1
                                      have p13608_3 := h13608c.2.2.2
                                      linarith only [hlam, p13608_0]
                              · linarith only [h0, h1, h13593, h13595, h13602, h13603, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · linarith only [h1, h13365, h13593, h13595, h13596, h13602, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · linarith only [h1, h13365, h13595, h13596, h13599, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h1, h13365, h13595, h13596, h13598, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h1, h13365, h13368, h13369, h13593, h13595, hc12, hc23, hlam, hphi]
            · linarith only [h1, h13365, h13590, hlam]
          · linarith only [h1, h13365, h13368, h13369, h13589, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h13655 | h13655
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13656 | h13656
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13657 | h13657
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13658 | h13658
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13659 | h13659
                · linarith only [h0, h1, h13366, h13659, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13661 | h13661
                  · linarith only [h0, h13368, h13661, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13663 | h13663
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13664 | h13664
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13665 | h13665
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13666 | h13666
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13667 | h13667
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13668 | h13668
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13669 | h13669
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13670 | h13670
                                  · rcases h0bigk with h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c | h13671c
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h1, h13659, hc02, hc23, hlam, hphi, p13671_1]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h1, hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h0, h1, h13368, h13659, hc12, hc23, hlam, hphi, p13671_1]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      rcases p13671_3 (m.d 0 1) (by simp) with h13676 | h13676
                                      · rcases p13671_3 (m.d 0 2) (by simp) with h13677 | h13677
                                        · linarith only [h0, h13677, hlam]
                                        · linarith only [h13655, h13677, hlam]
                                      · linarith only [h13365, h13676, hlam]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h0, hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h13366, hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h13368, hlam, p13671_1]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      rcases p13671_3 (m.d 0 1) (by simp) with h13685 | h13685
                                      · rcases p13671_3 (m.d 0 2) (by simp) with h13686 | h13686
                                        · rcases p13671_3 (m.d 0 3) (by simp) with h13687 | h13687
                                          · rcases p13671_3 (m.d 0 4) (by simp) with h13688 | h13688
                                            · rcases p13671_3 (m.d 0 5) (by simp) with h13689 | h13689
                                              · linarith only [h13655, h13689, hlam]
                                              · rcases h2bigk with h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c | h13691c
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13368, hc12, hc24, hlam, hphi, p13691_1]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13366, hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13368, hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  rcases p13691_3 (m.d 0 2) (by simp) with h13696 | h13696
                                                  · rcases p13691_3 (m.d 1 2) (by simp) with h13697 | h13697
                                                    · linarith only [h0, h13697, hlam]
                                                    · linarith only [h13663, h13697, hlam]
                                                  · linarith only [h13696, hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h0, hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13659, hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13661, hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h0, h1, h13659, h13668, h13670, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13691_1]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13365, h13663, h13668, h13670, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13671_1, p13691_1]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  rcases p13691_3 (m.d 0 2) (by simp) with h13707 | h13707
                                                  · linarith only [h13366, h13707, hlam]
                                                  · linarith only [h0, h13707, hlam]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13365, h13368, h13663, h13668, h13670, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13671_1, p13691_1]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h0, h1, h13365, h13659, h13663, hlam, p13671_1, p13691_2]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p13671_1, p13691_1]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  rcases p13691_3 (m.d 0 2) (by simp) with h13714 | h13714
                                                  · linarith only [h13368, h13714, hlam]
                                                  · linarith only [h0, h13714, hlam]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13667, hlam, p13691_1]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13365, h13368, h13663, hlam, p13671_1, p13691_2]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13655, hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13663, hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13668, hlam, p13691_1]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [h13669, hlam, p13691_0]
                                                · have p13691_0 := h13691c.1
                                                  have p13691_1 := h13691c.2.1
                                                  have p13691_2 := h13691c.2.2.1
                                                  have p13691_3 := h13691c.2.2.2
                                                  linarith only [hlam, p13691_0]
                                            · linarith only [h13658, h13688, hlam]
                                          · linarith only [h13657, h13687, hlam]
                                        · linarith only [h13655, h13686, hlam]
                                      · linarith only [h13365, h13685, hlam]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h13364, h13366, h13661, hc12, hc23, hlam, hphi, p13671_1]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      rcases p13671_3 (m.d 0 1) (by simp) with h13730 | h13730
                                      · linarith only [h1, h13730, hlam]
                                      · linarith only [h0, h13730, hlam]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      rcases p13671_3 (m.d 0 1) (by simp) with h13734 | h13734
                                      · linarith only [h1, h13734, hlam]
                                      · linarith only [h13364, h13734, hlam]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      rcases p13671_3 (m.d 0 1) (by simp) with h13737 | h13737
                                      · linarith only [h1, h13737, hlam]
                                      · linarith only [h13365, h13737, hlam]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h13364, hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h0, h1, h13364, h13659, h13663, h13668, h13670, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13671_1]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h13656, hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      rcases p13671_3 (m.d 0 1) (by simp) with h13744 | h13744
                                      · rcases p13671_3 (m.d 0 2) (by simp) with h13745 | h13745
                                        · linarith only [h13368, h13745, hlam]
                                        · linarith only [h13655, h13745, hlam]
                                      · linarith only [h13365, h13744, hlam]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h13365, hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h13655, hlam, p13671_1]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h13657, hlam, p13671_0]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [h13658, hlam, p13671_1]
                                    · have p13671_0 := h13671c.1
                                      have p13671_1 := h13671c.2.1
                                      have p13671_2 := h13671c.2.2.1
                                      have p13671_3 := h13671c.2.2.2
                                      linarith only [hlam, p13671_0]
                                  · linarith only [h1, h13364, h13659, h13666, h13670, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h13364, h13659, h13666, h13669, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h1, h13364, h13659, h13661, h13668, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h13364, h13659, h13666, h13667, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h13364, h13658, h13661, h13663, h13666, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h1, h13663, h13665, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h1, h13364, h13661, h13663, h13664, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · linarith only [h13366, h13655, h13663, hc12, hc23, hlam, hphi]
              · linarith only [h13368, h13655, h13658, hlam]
            · linarith only [h1, h13364, h13368, h13655, h13657, hlam]
          · linarith only [h1, h13364, h13656, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13765 | h13765
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13766 | h13766
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13767 | h13767
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13768 | h13768
                · linarith only [h0, h1, h13366, h13768, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13770 | h13770
                  · linarith only [h0, h13368, h13770, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13772 | h13772
                    · linarith only [h0, h13655, h13772, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13774 | h13774
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13775 | h13775
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13776 | h13776
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13777 | h13777
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13778 | h13778
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13779 | h13779
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13780 | h13780
                                  · rcases h0bigk with h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c | h13781c
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h0, h1, h13768, hc12, hc23, hlam, hphi, p13781_1]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h1, hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h1, h13364, h13768, h13774, h13780, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p13781_1]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h0, h1, h13655, h13768, hc12, hc23, hlam, hphi, p13781_1]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h0, hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h13366, hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h13368, hlam, p13781_1]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h13655, hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h0, h1, h13768, hc12, hc23, hlam, hphi, p13781_1]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      rcases p13781_3 (m.d 0 1) (by simp) with h13793 | h13793
                                      · linarith only [h1, h13793, hlam]
                                      · linarith only [h0, h13793, hlam]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      rcases p13781_3 (m.d 0 1) (by simp) with h13797 | h13797
                                      · linarith only [h1, h13797, hlam]
                                      · linarith only [h13364, h13797, hlam]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      rcases p13781_3 (m.d 0 1) (by simp) with h13800 | h13800
                                      · linarith only [h1, h13800, hlam]
                                      · linarith only [h13365, h13800, hlam]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h13364, hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h0, h1, h13364, h13768, hc12, hc23, hlam, hphi, p13781_1]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h13765, hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h0, h1, h13364, h13655, h13768, hc12, hc23, hlam, hphi, p13781_1]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h13365, hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h0, h1, h13365, h13768, hc12, hc23, hlam, hphi, p13781_1]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h13766, hlam, p13781_0]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [h13767, hlam, p13781_1]
                                    · have p13781_0 := h13781c.1
                                      have p13781_1 := h13781c.2.1
                                      have p13781_2 := h13781c.2.2.1
                                      have p13781_3 := h13781c.2.2.2
                                      linarith only [hlam, p13781_0]
                                  · linarith only [h1, h13364, h13768, h13776, h13780, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                                · linarith only [h1, h13364, h13368, h13768, h13776, h13779, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · linarith only [h0, h1, h13768, h13778, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h13364, h13768, h13776, h13777, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h1, h13364, h13767, h13768, h13770, h13776, hc12, hc23, hlam, hphi]
                        · linarith only [h0, h1, h13775, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h13774, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13820 | h13820
                · linarith only [h0, h13366, h13820, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13822 | h13822
                  · linarith only [h0, h13368, h13822, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13824 | h13824
                    · linarith only [h0, h13655, h13824, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13826 | h13826
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13827 | h13827
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13828 | h13828
                          · linarith only [h1, h13364, h13767, h13828, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13830 | h13830
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13831 | h13831
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13832 | h13832
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13833 | h13833
                                  · linarith only [h13364, h13767, h13826, h13833, hlam]
                                  · rcases h0bigk with h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c | h13835c
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h1, h13820, hc02, hc23, hlam, hphi, p13835_1]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h1, hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h0, h1, h13368, h13820, hc12, hc23, hlam, hphi, p13835_1]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h0, h1, h13655, h13820, hc12, hc23, hlam, hphi, p13835_1]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h0, hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h13366, hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h13368, hlam, p13835_1]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h13655, hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h0, h1, h13820, hc12, hc23, hlam, hphi, p13835_1]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      rcases p13835_3 (m.d 0 1) (by simp) with h13847 | h13847
                                      · linarith only [h1, h13847, hlam]
                                      · linarith only [h0, h13847, hlam]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      rcases p13835_3 (m.d 0 1) (by simp) with h13851 | h13851
                                      · linarith only [h1, h13851, hlam]
                                      · linarith only [h13364, h13851, hlam]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      rcases p13835_3 (m.d 0 1) (by simp) with h13854 | h13854
                                      · linarith only [h1, h13854, hlam]
                                      · linarith only [h13365, h13854, hlam]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h13364, hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h0, h13767, h13832, hc12, hc24, hlam, hphi, p13835_1]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h13765, hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h13767, hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h13365, hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h0, h1, h13365, h13820, hc12, hc23, hlam, hphi, p13835_1]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h13766, hlam, p13835_0]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [h0, h1, h13365, h13368, h13820, hc12, hc23, hlam, hphi, p13835_1]
                                    · have p13835_0 := h13835c.1
                                      have p13835_1 := h13835c.2.1
                                      have p13835_2 := h13835c.2.2.1
                                      have p13835_3 := h13835c.2.2.2
                                      linarith only [hlam, p13835_0]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13867 | h13867
                                  · linarith only [h0, h13368, h13832, h13867, hc12, hc34, hlam, hphi, ht23]
                                  · rcases h0bigk with h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c | h13869c
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h0, h1, h13820, hc12, hc23, hlam, hphi, p13869_1]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h1, hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h0, h1, h13368, h13820, hc12, hc23, hlam, hphi, p13869_1]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h0, h1, h13655, h13820, hc12, hc23, hlam, hphi, p13869_1]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h0, hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h13366, hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h13368, hlam, p13869_1]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h13655, hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h0, h1, h13820, hc12, hc23, hlam, hphi, p13869_1]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      rcases p13869_3 (m.d 0 1) (by simp) with h13881 | h13881
                                      · linarith only [h1, h13881, hlam]
                                      · linarith only [h0, h13881, hlam]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      rcases p13869_3 (m.d 0 1) (by simp) with h13885 | h13885
                                      · linarith only [h1, h13885, hlam]
                                      · linarith only [h13364, h13885, hlam]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      rcases p13869_3 (m.d 0 1) (by simp) with h13888 | h13888
                                      · linarith only [h1, h13888, hlam]
                                      · linarith only [h13365, h13888, hlam]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h13364, hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h0, h1, h13364, h13820, hc12, hc23, hlam, hphi, p13869_1]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h13765, hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h13767, hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h13365, hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h0, h1, h13365, h13820, hc12, hc23, hlam, hphi, p13869_1]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h13766, hlam, p13869_0]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [h0, h1, h13365, h13368, h13820, hc12, hc23, hlam, hphi, p13869_1]
                                    · have p13869_0 := h13869c.1
                                      have p13869_1 := h13869c.2.1
                                      have p13869_2 := h13869c.2.2.1
                                      have p13869_3 := h13869c.2.2.2
                                      linarith only [hlam, p13869_0]
                              · linarith only [h0, h1, h13820, h13831, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h13365, h13820, h13822, h13828, h13830, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1, h13827, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h0, h1, h13826, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h13365, h13766, hlam]
          · linarith only [h1, h13364, h13765, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h13907 | h13907
    · linarith only [h0, h1, h13907, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h13909 | h13909
      · rcases m.htr 0 2 5 (by decide) (by decide) with h13910 | h13910
        · linarith only [h0, h13365, h13910, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13912 | h13912
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13913 | h13913
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13914 | h13914
              · linarith only [h0, h13365, h13909, h13914, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13916 | h13916
                · linarith only [h0, h1, h13907, h13916, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13918 | h13918
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13919 | h13919
                    · linarith only [h0, h13365, h13910, h13919, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13921 | h13921
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13922 | h13922
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13923 | h13923
                          · linarith only [h0, h13364, h13365, h13909, h13914, h13923, hlam]
                          · linarith only [h0, h13365, h13918, h13923, hc24, hc45, hlam, hphi]
                        · linarith only [h0, h1, h13913, h13918, h13922, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h0, h1, h13918, h13921, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h13907, h13909, h13918, hc12, hc23, hlam, hphi]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13929 | h13929
              · linarith only [h0, h1, h13909, h13913, h13929, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13931 | h13931
                · linarith only [h0, h1, h13907, h13931, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13933 | h13933
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13934 | h13934
                    · linarith only [h0, h13910, h13934, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13936 | h13936
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13937 | h13937
                        · linarith only [h0, h1, h13913, h13931, h13933, h13937, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1, h13933, h13937, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                      · linarith only [h0, h1, h13933, h13936, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h13907, h13909, h13933, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h13909, h13912, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h13943 | h13943
        · linarith only [h13364, h13365, h13909, h13943, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h13945 | h13945
          · rcases m.htr 0 3 5 (by decide) (by decide) with h13946 | h13946
            · rcases m.htr 0 4 5 (by decide) (by decide) with h13947 | h13947
              · linarith only [h13364, h13365, h13947, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h13949 | h13949
                · linarith only [h0, h13907, h13949, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h13951 | h13951
                  · linarith only [h0, h13909, h13951, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h13953 | h13953
                    · linarith only [h0, h13365, h13943, h13953, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13955 | h13955
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h13956 | h13956
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13957 | h13957
                          · linarith only [h13364, h13365, h13909, h13947, h13956, h13957, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h13959 | h13959
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h13960 | h13960
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h13961 | h13961
                                · linarith only [h0, h13365, h13957, h13959, h13961, hc12, hc23, hlam, hphi]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h13963 | h13963
                                  · linarith only [h13364, h13365, h13955, h13961, h13963, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h0bigk with h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c | h13965c
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13365, h13953, h13961, hc02, hc45, hlam, hphi, ht23, ht34, p13965_1]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h1, hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h0, h13365, h13909, h13953, h13961, hc12, hc45, hlam, hphi, ht23, ht34, p13965_1]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13365, hlam, p13965_1]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h0, hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13907, hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13909, hlam, p13965_1]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13943, hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h0, h13907, hc12, hc23, hlam, hphi, p13965_1]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      rcases p13965_3 (m.d 0 1) (by simp) with h13977 | h13977
                                      · linarith only [h1, h13977, hlam]
                                      · linarith only [h0, h13977, hlam]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      rcases p13965_3 (m.d 0 1) (by simp) with h13981 | h13981
                                      · linarith only [h1, h13981, hlam]
                                      · linarith only [h13364, h13981, hlam]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h1, h13364, h13365, h13949, h13951, hc12, hc23, hlam, hphi, p13965_1]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13364, hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h0, h13364, h13365, h13953, hc12, hc25, hlam, hphi, p13965_1]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13945, hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13947, hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13364, h13365, h13951, h13953, h13961, hc12, hc45, hlam, hphi, ht23, ht34, p13965_1]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      rcases p13965_3 (m.d 0 1) (by simp) with h13991 | h13991
                                      · linarith only [h13365, h13991, hlam]
                                      · linarith only [h0, h13991, hlam]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [h13946, hlam, p13965_0]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      rcases p13965_3 (m.d 0 1) (by simp) with h13995 | h13995
                                      · linarith only [h13365, h13995, hlam]
                                      · linarith only [h13364, h13995, hlam]
                                    · have p13965_0 := h13965c.1
                                      have p13965_1 := h13965c.2.1
                                      have p13965_2 := h13965c.2.2.1
                                      have p13965_3 := h13965c.2.2.2
                                      linarith only [hlam, p13965_0]
                              · linarith only [h1, h13946, h13949, h13960, hlam]
                            · linarith only [h1, h13364, h13949, h13955, h13959, hlam]
                        · linarith only [h1, h13946, h13956, hlam]
                      · linarith only [h1, h13364, h13951, h13955, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h14003 | h14003
              · linarith only [h13364, h13365, h14003, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h14005 | h14005
                · linarith only [h0, h1, h13946, h14005, hc23, hc35, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h14007 | h14007
                  · linarith only [h0, h13909, h14007, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h14009 | h14009
                    · linarith only [h0, h13943, h14009, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h14011 | h14011
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h14012 | h14012
                        · linarith only [h0, h1, h13946, h14005, h14012, hc12, hc23, hlam, hphi]
                        · linarith only [h1, h13364, h14007, h14012, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h13364, h14007, h14011, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h13364, h13945, hlam]

end R2N4
