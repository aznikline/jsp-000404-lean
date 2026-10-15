import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 16662000 in
set_option maxHeartbeats 16662000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s18_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg18815 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h20408 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h26804 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h27373 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h14396 := hg14396
  have h16915 := hg16915
  have h18815 := hg18815
  rcases m.htr 0 3 4 (by decide) (by decide) with h27374 | h27374
  · rcases m.htr 0 3 5 (by decide) (by decide) with h27375 | h27375
    · rcases m.htr 0 4 5 (by decide) (by decide) with h27376 | h27376
      · rcases m.htr 1 2 3 (by decide) (by decide) with h27377 | h27377
        · rcases m.htr 1 2 4 (by decide) (by decide) with h27378 | h27378
          · rcases m.htr 1 2 5 (by decide) (by decide) with h27379 | h27379
            · rcases m.htr 1 3 4 (by decide) (by decide) with h27380 | h27380
              · rcases m.htr 1 3 5 (by decide) (by decide) with h27381 | h27381
                · rcases m.htr 1 4 5 (by decide) (by decide) with h27382 | h27382
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h27383 | h27383
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h27384 | h27384
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h27385 | h27385
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h27386 | h27386
                          · rcases h0bigk with h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c | h27387c
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [hlam, p27387_0]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h0, hlam, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h14396, hlam, p27387_0]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h16915, hlam, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h18815, hlam, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h26804, h27377, h27383, hc01, hc12, hlam, hphi, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [hlam, p27387_0]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h20408, hlam, p27387_0]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h26804, hlam, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h26804, h27377, h27383, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h20408, h27377, hc01, hc12, hlam, hphi, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h20408, h27373, h27377, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [hlam, p27387_0]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h16915, h20408, h27377, hc01, hc12, hlam, hphi, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h18815, h20408, h27377, hc01, hc12, hlam, hphi, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h26804, h27377, h27383, hc01, hc12, hlam, hphi, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h26804, h27373, h27377, h27383, h27384, h27386, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h27374, hlam, p27387_0]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [hlam, p27387_0]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h18815, h26804, h27377, h27383, hc01, hc12, hlam, hphi, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h20408, h27373, h27377, hc01, hc12, hlam, hphi, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h27373, hlam, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h27375, hlam, p27387_0]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [h27376, hlam, p27387_1]
                            · have p27387_0 := h27387c.1
                              have p27387_1 := h27387c.2.1
                              have p27387_2 := h27387c.2.2.1
                              have p27387_3 := h27387c.2.2.2
                              linarith only [hlam, p27387_0]
                          · linarith only [h26804, h27373, h27377, h27383, h27385, h27386, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h26804, h27376, h27385, hlam]
                      · linarith only [h20408, h27375, h27384, hlam]
                    · linarith only [h20408, h27374, h27383, hlam]
                  · linarith only [h16915, h26804, h27373, h27376, h27382, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h14396, h20408, h27373, h27375, h27381, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h20408, h27374, h27377, h27380, hlam]
            · linarith only [h20408, h27373, h27379, hc12, hc23, hlam, hphi]
          · linarith only [h18815, h20408, h27373, h27377, h27378, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h27422 | h27422
          · linarith only [h18815, h26804, h27373, h27377, h27422, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h27424 | h27424
            · rcases m.htr 1 3 4 (by decide) (by decide) with h27425 | h27425
              · rcases m.htr 1 3 5 (by decide) (by decide) with h27426 | h27426
                · rcases m.htr 1 4 5 (by decide) (by decide) with h27427 | h27427
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h27428 | h27428
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h27429 | h27429
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h27430 | h27430
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h27431 | h27431
                          · rcases h0bigk with h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c | h27432c
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [hlam, p27432_0]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h0, hlam, p27432_1]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h14396, hlam, p27432_0]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h16915, hlam, p27432_1]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h18815, hlam, p27432_1]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h0, h27422, h27428, hc01, hc23, hlam, hphi, ht12, p27432_1]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [hlam, p27432_0]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h20408, hlam, p27432_0]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h26804, hlam, p27432_1]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h0, h18815, h27422, h27428, hc01, hc23, hlam, hphi, ht12, p27432_1]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              rcases p27432_3 (m.d 0 1) (by simp) with h27443 | h27443
                              · linarith only [h14396, h27443, hlam]
                              · rcases p27432_3 (m.d 0 2) (by simp) with h27445 | h27445
                                · linarith only [h20408, h27445, hlam]
                                · linarith only [h0, h27445, hlam]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              rcases p27432_3 (m.d 0 1) (by simp) with h27448 | h27448
                              · linarith only [h14396, h27448, hlam]
                              · rcases p27432_3 (m.d 0 2) (by simp) with h27450 | h27450
                                · linarith only [h20408, h27450, hlam]
                                · rcases p27432_3 (m.d 0 3) (by simp) with h27452 | h27452
                                  · rcases p27432_3 (m.d 0 4) (by simp) with h27453 | h27453
                                    · linarith only [h27374, h27453, hlam]
                                    · linarith only [h26804, h27453, hlam]
                                  · linarith only [h20408, h27452, hlam]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [hlam, p27432_0]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              rcases p27432_3 (m.d 0 1) (by simp) with h27458 | h27458
                              · linarith only [h14396, h27458, hlam]
                              · rcases p27432_3 (m.d 0 2) (by simp) with h27460 | h27460
                                · linarith only [h20408, h27460, hlam]
                                · rcases p27432_3 (m.d 0 3) (by simp) with h27462 | h27462
                                  · rcases p27432_3 (m.d 0 4) (by simp) with h27463 | h27463
                                    · linarith only [h27374, h27463, hlam]
                                    · rcases p27432_3 (m.d 0 5) (by simp) with h27465 | h27465
                                      · linarith only [h27375, h27465, hlam]
                                      · rcases h2bigk with h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c | h27467c
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h0, hlam, p27467_1]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h20408, hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h26804, hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h14396, h26804, h27377, h27429, h27431, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p27432_1, p27467_1]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h27422, h27428, hc02, hc23, hlam, hphi, p27467_1]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h27377, hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h27422, hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          rcases p27467_3 (m.d 0 2) (by simp) with h27477 | h27477
                                          · linarith only [h0, h27477, hlam]
                                          · linarith only [h27373, h27477, hlam]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          rcases p27467_3 (m.d 0 2) (by simp) with h27480 | h27480
                                          · linarith only [h27480, hlam, p27467_0]
                                          · rcases p27467_3 (m.d 1 2) (by simp) with h27482 | h27482
                                            · linarith only [h27377, h27482, hlam]
                                            · linarith only [h0, h27482, hlam]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p27467_1]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h26804, h27373, h27429, h27431, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p27467_1]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h14396, h26804, h27373, h27377, hlam, p27432_1, p27467_2]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          rcases p27467_3 (m.d 0 2) (by simp) with h27489 | h27489
                                          · linarith only [h27489, hlam, p27467_0]
                                          · rcases p27467_3 (m.d 1 2) (by simp) with h27491 | h27491
                                            · linarith only [h27422, h27491, hlam]
                                            · linarith only [h0, h27491, hlam]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h18815, h27424, hc01, hc24, hlam, hphi, ht12, p27467_1]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h27428, hlam, p27467_1]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          rcases p27467_3 (m.d 0 2) (by simp) with h27497 | h27497
                                          · linarith only [h26804, h27497, hlam]
                                          · linarith only [h27373, h27497, hlam]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h27373, hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h27424, hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h27429, hlam, p27467_1]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [h27430, hlam, p27467_0]
                                        · have p27467_0 := h27467c.1
                                          have p27467_1 := h27467c.2.1
                                          have p27467_2 := h27467c.2.2.1
                                          have p27467_3 := h27467c.2.2.2
                                          linarith only [hlam, p27467_0]
                                  · linarith only [h27374, h27462, hlam]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              rcases p27432_3 (m.d 0 1) (by simp) with h27506 | h27506
                              · linarith only [h14396, h27506, hlam]
                              · rcases p27432_3 (m.d 0 2) (by simp) with h27508 | h27508
                                · linarith only [h20408, h27508, hlam]
                                · linarith only [h27373, h27508, hlam]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              rcases p27432_3 (m.d 0 1) (by simp) with h27511 | h27511
                              · linarith only [h16915, h27511, hlam]
                              · rcases p27432_3 (m.d 0 2) (by simp) with h27513 | h27513
                                · linarith only [h26804, h27513, hlam]
                                · linarith only [h0, h27513, hlam]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              rcases p27432_3 (m.d 0 1) (by simp) with h27516 | h27516
                              · linarith only [h16915, h27516, hlam]
                              · rcases p27432_3 (m.d 0 2) (by simp) with h27518 | h27518
                                · linarith only [h26804, h27518, hlam]
                                · rcases p27432_3 (m.d 0 3) (by simp) with h27520 | h27520
                                  · rcases p27432_3 (m.d 0 4) (by simp) with h27521 | h27521
                                    · rcases p27432_3 (m.d 0 5) (by simp) with h27522 | h27522
                                      · linarith only [h27376, h27522, hlam]
                                      · rcases h2bigk with h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c | h27524c
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h0, hlam, p27524_1]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h20408, hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h26804, hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h27429, h27431, hc04, hc45, hlam, hphi, ht0b, ht5b, p27432_1, p27524_1]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h27377, hc02, hc23, hlam, hphi, p27524_1]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h27377, hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h27422, hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          rcases p27524_3 (m.d 0 2) (by simp) with h27534 | h27534
                                          · linarith only [h0, h27534, hlam]
                                          · linarith only [h27373, h27534, hlam]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          rcases p27524_3 (m.d 0 2) (by simp) with h27537 | h27537
                                          · linarith only [h27537, hlam, p27524_0]
                                          · rcases p27524_3 (m.d 1 2) (by simp) with h27539 | h27539
                                            · linarith only [h27377, h27539, hlam]
                                            · linarith only [h0, h27539, hlam]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h0, hc01, hc23, hlam, hphi, ht12, p27524_1]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h26804, h27373, h27429, h27431, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p27524_1]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h14396, h27373, h27374, h27377, hlam, p27432_1, p27524_2]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          rcases p27524_3 (m.d 0 2) (by simp) with h27546 | h27546
                                          · linarith only [h27546, hlam, p27524_0]
                                          · rcases p27524_3 (m.d 1 2) (by simp) with h27548 | h27548
                                            · linarith only [h27422, h27548, hlam]
                                            · linarith only [h0, h27548, hlam]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h18815, h27424, h27428, hc01, hc23, hlam, hphi, ht12, p27524_1]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h27428, hlam, p27524_1]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h26804, h27373, hlam, p27432_1, p27524_2]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h27373, hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h27424, hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h27429, hlam, p27524_1]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [h27430, hlam, p27524_0]
                                        · have p27524_0 := h27524c.1
                                          have p27524_1 := h27524c.2.1
                                          have p27524_2 := h27524c.2.2.1
                                          have p27524_3 := h27524c.2.2.2
                                          linarith only [hlam, p27524_0]
                                    · linarith only [h26804, h27521, hlam]
                                  · linarith only [h20408, h27520, hlam]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h27374, hlam, p27432_0]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [hlam, p27432_0]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              rcases p27432_3 (m.d 0 1) (by simp) with h27564 | h27564
                              · linarith only [h16915, h27564, hlam]
                              · rcases p27432_3 (m.d 0 2) (by simp) with h27566 | h27566
                                · linarith only [h26804, h27566, hlam]
                                · linarith only [h27373, h27566, hlam]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h20408, h27373, hc01, hc23, hlam, hphi, ht12, p27432_1]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h27373, hlam, p27432_1]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h27375, hlam, p27432_0]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [h27376, hlam, p27432_1]
                            · have p27432_0 := h27432c.1
                              have p27432_1 := h27432c.2.1
                              have p27432_2 := h27432c.2.2.1
                              have p27432_3 := h27432c.2.2.2
                              linarith only [hlam, p27432_0]
                          · rcases h0bigk with h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c | h27574c
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [hlam, p27574_0]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h0, hlam, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h14396, hlam, p27574_0]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h16915, hlam, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h18815, hlam, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h0, h27422, h27428, hc01, hc23, hlam, hphi, ht12, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [hlam, p27574_0]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h20408, hlam, p27574_0]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h26804, hlam, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h0, h18815, h27422, h27428, hc01, hc23, hlam, hphi, ht12, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              rcases p27574_3 (m.d 0 1) (by simp) with h27585 | h27585
                              · linarith only [h14396, h27585, hlam]
                              · rcases p27574_3 (m.d 0 2) (by simp) with h27587 | h27587
                                · linarith only [h20408, h27587, hlam]
                                · linarith only [h0, h27587, hlam]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h14396, h27373, h27377, h27430, h27431, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [hlam, p27574_0]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h14396, h26804, h27373, h27377, h27430, h27431, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              rcases p27574_3 (m.d 0 1) (by simp) with h27593 | h27593
                              · linarith only [h14396, h27593, hlam]
                              · rcases p27574_3 (m.d 0 2) (by simp) with h27595 | h27595
                                · linarith only [h20408, h27595, hlam]
                                · linarith only [h27373, h27595, hlam]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              rcases p27574_3 (m.d 0 1) (by simp) with h27598 | h27598
                              · linarith only [h16915, h27598, hlam]
                              · rcases p27574_3 (m.d 0 2) (by simp) with h27600 | h27600
                                · linarith only [h26804, h27600, hlam]
                                · linarith only [h0, h27600, hlam]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h27373, h27430, h27431, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h27374, hlam, p27574_0]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [hlam, p27574_0]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              rcases p27574_3 (m.d 0 1) (by simp) with h27606 | h27606
                              · linarith only [h16915, h27606, hlam]
                              · rcases p27574_3 (m.d 0 2) (by simp) with h27608 | h27608
                                · linarith only [h26804, h27608, hlam]
                                · linarith only [h27373, h27608, hlam]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h18815, h27422, h27424, h27428, hc01, hc23, hlam, hphi, ht12, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h27373, hlam, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h27375, hlam, p27574_0]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [h27376, hlam, p27574_1]
                            · have p27574_0 := h27574c.1
                              have p27574_1 := h27574c.2.1
                              have p27574_2 := h27574c.2.2.1
                              have p27574_3 := h27574c.2.2.2
                              linarith only [hlam, p27574_0]
                        · linarith only [h0, h27422, h27430, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h27422, h27428, h27429, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h14396, h27374, h27377, h27428, hlam]
                  · linarith only [h0, h16915, h27373, h27376, h27377, h27427, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h0, h14396, h27373, h27375, h27377, h27426, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h14396, h27374, h27425, hlam]
            · linarith only [h0, h27373, h27424, hlam]
      · linarith only [h26804, h27373, h27376, hlam]
    · linarith only [h20408, h27373, h27375, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h27625 | h27625
    · rcases m.htr 0 4 5 (by decide) (by decide) with h27626 | h27626
      · rcases m.htr 1 2 3 (by decide) (by decide) with h27627 | h27627
        · rcases m.htr 1 2 4 (by decide) (by decide) with h27628 | h27628
          · rcases m.htr 1 2 5 (by decide) (by decide) with h27629 | h27629
            · rcases m.htr 1 3 4 (by decide) (by decide) with h27630 | h27630
              · rcases m.htr 1 3 5 (by decide) (by decide) with h27631 | h27631
                · rcases m.htr 1 4 5 (by decide) (by decide) with h27632 | h27632
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h27633 | h27633
                    · linarith only [h20408, h27373, h27374, h27627, h27633, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h20408, h27373, h27627, h27630, h27633, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h16915, h27626, h27632, hlam]
                · linarith only [h14396, h27625, h27631, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h27638 | h27638
                · rcases m.htr 1 4 5 (by decide) (by decide) with h27639 | h27639
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h27640 | h27640
                    · linarith only [h27627, h27630, h27640, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h27642 | h27642
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h27643 | h27643
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h27644 | h27644
                          · rcases h0bigk with h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c | h27645c
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [hlam, p27645_0]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h0, hlam, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h14396, hlam, p27645_0]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h16915, hlam, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h18815, hlam, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h20408, h27627, h27630, hc01, hc34, hlam, hphi, ht12, ht23, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [hlam, p27645_0]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h20408, hlam, p27645_0]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h26804, hlam, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h18815, h20408, h27627, h27630, hc01, hc34, hlam, hphi, ht12, ht23, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h20408, h27627, h27630, hc01, hc34, hlam, hphi, ht12, ht23, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h20408, h27627, h27630, hc02, hc34, hlam, hphi, ht23, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [hlam, p27645_0]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h27374, hlam, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h18815, h20408, h27627, h27630, hc01, hc34, hlam, hphi, ht12, ht23, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h26804, h27628, hc01, hc12, hlam, hphi, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h26804, h27373, h27628, h27642, h27644, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h20408, h26804, h27373, h27628, h27642, h27644, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [hlam, p27645_0]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h18815, h26804, h27628, hc01, hc12, hlam, hphi, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h14396, h20408, h27373, h27630, hc01, hc34, hlam, hphi, ht12, ht23, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h27373, hlam, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h27625, hlam, p27645_0]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [h27626, hlam, p27645_1]
                            · have p27645_0 := h27645c.1
                              have p27645_1 := h27645c.2.1
                              have p27645_2 := h27645c.2.2.1
                              have p27645_3 := h27645c.2.2.2
                              linarith only [hlam, p27645_0]
                          · linarith only [h20408, h27627, h27630, h27644, hc02, hc45, hlam, hphi, ht23, ht34]
                        · linarith only [h16915, h20408, h26804, h27373, h27626, h27627, h27630, h27643, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h20408, h27625, h27642, hlam]
                  · linarith only [h20408, h26804, h27373, h27374, h27626, h27627, h27628, h27630, h27639, hc03, hc34, hlam, hphi]
                · linarith only [h20408, h27373, h27374, h27625, h27627, h27638, hc04, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h27373, h27629, hlam]
          · linarith only [h20408, h27627, h27628, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h27678 | h27678
          · linarith only [h26804, h27373, h27627, h27678, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h27680 | h27680
            · rcases m.htr 1 3 4 (by decide) (by decide) with h27681 | h27681
              · rcases m.htr 1 3 5 (by decide) (by decide) with h27682 | h27682
                · rcases m.htr 1 4 5 (by decide) (by decide) with h27683 | h27683
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h27684 | h27684
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h27685 | h27685
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h27686 | h27686
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h27687 | h27687
                          · rcases h0bigk with h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c | h27688c
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [hlam, p27688_0]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h0, hlam, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h14396, hlam, p27688_0]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h16915, hlam, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h18815, hlam, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h20408, h27374, h27681, hc01, hc13, hlam, hphi, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [hlam, p27688_0]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h20408, hlam, p27688_0]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h26804, hlam, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h20408, h27374, h27681, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h27374, h27681, hc01, hc13, hlam, hphi, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h27374, h27681, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [hlam, p27688_0]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h27374, hlam, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h18815, h27374, h27681, hc01, hc13, hlam, hphi, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h27374, h27681, hc01, hc13, hlam, hphi, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h27373, h27374, h27681, h27685, h27687, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h14396, h27374, h27681, hc01, hc13, hlam, hphi, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [hlam, p27688_0]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h18815, h27374, h27681, hc01, hc13, hlam, hphi, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h0, h27373, h27678, h27684, hc01, hc23, hlam, hphi, ht12, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h27373, hlam, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h27625, hlam, p27688_0]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [h27626, hlam, p27688_1]
                            · have p27688_0 := h27688c.1
                              have p27688_1 := h27688c.2.1
                              have p27688_2 := h27688c.2.2.1
                              have p27688_3 := h27688c.2.2.2
                              linarith only [hlam, p27688_0]
                          · linarith only [h27374, h27626, h27687, hlam]
                        · linarith only [h20408, h27373, h27374, h27626, h27678, h27686, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h20408, h27374, h27627, h27681, h27685, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h27627, h27681, h27684, hlam]
                  · linarith only [h16915, h20408, h27373, h27374, h27626, h27627, h27681, h27683, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h27374, h27625, h27681, h27682, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h27720 | h27720
                · rcases m.htr 1 4 5 (by decide) (by decide) with h27721 | h27721
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h27722 | h27722
                    · linarith only [h18815, h27627, h27680, h27681, h27722, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h18815, h27627, h27680, h27722, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h16915, h27373, h27626, h27627, h27721, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h14396, h27625, h27720, hlam]
            · linarith only [h0, h14396, h20408, h27373, h27680, hc01, hc13, hlam, hphi]
      · linarith only [h20408, h27373, h27374, h27626, hlam]
    · linarith only [h20408, h27373, h27625, hlam]

end R2N4
