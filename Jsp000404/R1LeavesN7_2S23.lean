import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14401 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h14402 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h14403 | h14403
  · rcases m.htr 0 4 5 (by decide) (by decide) with h14404 | h14404
    · rcases m.htr 1 2 3 (by decide) (by decide) with h14405 | h14405
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14406 | h14406
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14407 | h14407
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14408 | h14408
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14409 | h14409
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14410 | h14410
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14411 | h14411
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14412 | h14412
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14413 | h14413
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14414 | h14414
                        · linarith only [h0, h14396, h14405, h14411, h14414, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h14396, h14408, h14410, h14414, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h14396, h14408, h14410, h14413, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h0, h14396, h14409, h14412, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h14396, h14408, h14411, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14420 | h14420
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14421 | h14421
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14422 | h14422
                      · linarith only [h14406, h14410, h14422, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14424 | h14424
                        · linarith only [h14399, h14410, h14420, h14424, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases h0bigk with h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c | h14426c
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [hlam, p14426_0]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h0, hlam, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h0, h14396, h14405, h14421, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h0, h14404, h14406, h14410, h14420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h0, h14404, h14406, h14410, h14420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h0, h14396, h14405, h14421, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [hlam, p14426_0]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h0, h14402, h14404, h14406, h14410, h14420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h0, h14404, h14406, h14410, h14420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            rcases p14426_3 (m.d 0 1) (by simp) with h14436 | h14436
                            · linarith only [h0, h14436, hlam]
                            · linarith only [h14398, h14436, hlam]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14396, hlam, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14399, hlam, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [hlam, p14426_0]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14396, h14404, h14406, h14410, h14420, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h0, h14396, h14404, h14406, h14410, h14420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14397, hlam, p14426_0]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14400, hlam, p14426_0]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14402, hlam, p14426_0]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [hlam, p14426_0]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h0, h14397, h14404, h14406, h14410, h14420, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14398, hlam, p14426_0]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14401, hlam, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14403, hlam, p14426_0]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [h14404, hlam, p14426_1]
                          · have p14426_0 := h14426c.1
                            have p14426_1 := h14426c.2.1
                            have p14426_2 := h14426c.2.2.1
                            have p14426_3 := h14426c.2.2.2
                            linarith only [hlam, p14426_0]
                    · linarith only [h0, h14396, h14409, h14421, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h14396, h14408, h14420, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h14396, h14403, h14408, h14409, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14457 | h14457
              · linarith only [h0, h14396, h14402, h14408, h14457, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14459 | h14459
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14460 | h14460
                  · linarith only [h14405, h14408, h14460, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14462 | h14462
                    · linarith only [h14405, h14457, h14462, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14464 | h14464
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14465 | h14465
                        · rcases h0bigk with h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c | h14466c
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [hlam, p14466_0]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h0, hlam, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h0, h14402, h14457, h14465, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h0, h14397, h14406, h14464, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h0, h14403, h14457, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h0, h14396, h14402, h14457, h14465, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [hlam, p14466_0]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h0, h14402, h14457, h14465, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            rcases p14466_3 (m.d 0 1) (by simp) with h14475 | h14475
                            · linarith only [h0, h14475, hlam]
                            · linarith only [h14397, h14475, hlam]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            rcases p14466_3 (m.d 0 1) (by simp) with h14478 | h14478
                            · linarith only [h0, h14478, hlam]
                            · linarith only [h14398, h14478, hlam]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h14396, hlam, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h14399, hlam, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [hlam, p14466_0]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h0, h14396, h14402, h14405, h14457, h14465, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h0, h14396, h14403, h14405, h14457, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h14397, hlam, p14466_0]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h14400, hlam, p14466_0]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h14402, hlam, p14466_0]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [hlam, p14466_0]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h0, h14397, h14403, h14405, h14457, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h14398, hlam, p14466_0]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h14401, hlam, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h14403, hlam, p14466_0]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [h14404, hlam, p14466_1]
                          · have p14466_0 := h14466c.1
                            have p14466_1 := h14466c.2.1
                            have p14466_2 := h14466c.2.2.1
                            have p14466_3 := h14466c.2.2.2
                            linarith only [hlam, p14466_0]
                        · linarith only [h0, h14397, h14406, h14464, h14465, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h14396, h14402, h14408, h14459, h14464, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14498 | h14498
                  · linarith only [h0, h14396, h14403, h14405, h14457, h14498, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14500 | h14500
                    · linarith only [h0, h14396, h14402, h14404, h14405, h14408, h14459, h14500, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14502 | h14502
                      · linarith only [h14406, h14459, h14502, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14504 | h14504
                        · linarith only [h0, h14396, h14402, h14459, h14504, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h14396, h14402, h14404, h14405, h14408, h14504, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h14401, h14407, hlam]
        · linarith only [h0, h14400, h14406, hlam]
      · linarith only [h0, h14399, h14405, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h14510 | h14510
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14511 | h14511
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14512 | h14512
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14513 | h14513
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14514 | h14514
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14515 | h14515
                · linarith only [h0, h14397, h14404, h14515, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14517 | h14517
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14518 | h14518
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14519 | h14519
                      · linarith only [h14397, h14404, h14511, h14519, hlam]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14521 | h14521
                        · linarith only [h0, h14399, h14404, h14517, h14521, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases h0bigk with h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c | h14523c
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h0, hlam, p14523_1]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h0, h14396, h14510, h14518, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14523_1]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            rcases p14523_3 (m.d 0 1) (by simp) with h14527 | h14527
                            · rcases p14523_3 (m.d 0 2) (by simp) with h14528 | h14528
                              · rcases p14523_3 (m.d 0 3) (by simp) with h14529 | h14529
                                · linarith only [h14396, h14529, hlam]
                                · linarith only [h14402, h14529, hlam]
                              · linarith only [h14400, h14528, hlam]
                            · linarith only [h14397, h14527, hlam]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            rcases p14523_3 (m.d 0 1) (by simp) with h14534 | h14534
                            · rcases p14523_3 (m.d 0 2) (by simp) with h14535 | h14535
                              · rcases p14523_3 (m.d 0 3) (by simp) with h14536 | h14536
                                · linarith only [h14396, h14536, hlam]
                                · linarith only [h14403, h14536, hlam]
                              · linarith only [h14401, h14535, hlam]
                            · linarith only [h14398, h14534, hlam]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h0, h14396, h14510, h14518, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14523_1]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            rcases p14523_3 (m.d 0 1) (by simp) with h14543 | h14543
                            · linarith only [h0, h14543, hlam]
                            · linarith only [h14396, h14543, hlam]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            rcases p14523_3 (m.d 0 1) (by simp) with h14546 | h14546
                            · linarith only [h0, h14546, hlam]
                            · linarith only [h14397, h14546, hlam]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            rcases p14523_3 (m.d 0 1) (by simp) with h14549 | h14549
                            · linarith only [h0, h14549, hlam]
                            · linarith only [h14398, h14549, hlam]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h14396, hlam, p14523_1]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h14399, hlam, p14523_1]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            rcases p14523_3 (m.d 0 1) (by simp) with h14555 | h14555
                            · rcases p14523_3 (m.d 0 2) (by simp) with h14556 | h14556
                              · rcases p14523_3 (m.d 0 3) (by simp) with h14557 | h14557
                                · rcases p14523_3 (m.d 0 4) (by simp) with h14558 | h14558
                                  · linarith only [h14402, h14558, hlam]
                                  · rcases p14523_3 (m.d 0 5) (by simp) with h14560 | h14560
                                    · linarith only [h14403, h14560, hlam]
                                    · linarith only [h14404, h14560, hlam]
                                · linarith only [h14402, h14557, hlam]
                              · linarith only [h14400, h14556, hlam]
                            · linarith only [h14397, h14555, hlam]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            rcases p14523_3 (m.d 0 1) (by simp) with h14566 | h14566
                            · rcases p14523_3 (m.d 0 2) (by simp) with h14567 | h14567
                              · rcases p14523_3 (m.d 0 3) (by simp) with h14568 | h14568
                                · rcases p14523_3 (m.d 0 4) (by simp) with h14569 | h14569
                                  · linarith only [h14402, h14569, hlam]
                                  · rcases p14523_3 (m.d 0 5) (by simp) with h14571 | h14571
                                    · linarith only [h14403, h14571, hlam]
                                    · rcases h2bigk with h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c | h14573c
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h0, hlam, p14573_1]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        rcases p14573_3 (m.d 0 2) (by simp) with h14576 | h14576
                                        · rcases p14573_3 (m.d 1 2) (by simp) with h14577 | h14577
                                          · rcases p14573_3 (m.d 2 3) (by simp) with h14578 | h14578
                                            · linarith only [h14578, hlam, p14573_0]
                                            · rcases p14573_3 (m.d 2 4) (by simp) with h14580 | h14580
                                              · linarith only [h14400, h14580, hlam]
                                              · rcases p14573_3 (m.d 2 5) (by simp) with h14582 | h14582
                                                · linarith only [h14401, h14582, hlam]
                                                · rcases h3bigk with h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c | h14584c
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14396, h14510, h14518, h14521, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h0, h14396, h14518, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h0, h14396, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h0, h14396, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14396, hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14518, h14521, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h0, h14396, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h0, h14396, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14399, hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14510, hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p14573_1, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h0, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14573_1, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14402, hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14513, hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14517, hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14521, hlam, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14403, hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14514, hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h14518, hlam, p14584_0]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [h0, h14396, h14403, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14584_1]
                                                  · have p14584_0 := h14584c.1
                                                    have p14584_1 := h14584c.2.1
                                                    have p14584_2 := h14584c.2.2.1
                                                    have p14584_3 := h14584c.2.2.2
                                                    linarith only [hlam, p14584_0]
                                          · linarith only [h14510, h14577, hlam]
                                        · linarith only [h14576, hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        rcases p14573_3 (m.d 0 2) (by simp) with h14612 | h14612
                                        · rcases p14573_3 (m.d 1 2) (by simp) with h14613 | h14613
                                          · rcases p14573_3 (m.d 2 3) (by simp) with h14614 | h14614
                                            · linarith only [h14399, h14614, hlam]
                                            · linarith only [h14517, h14614, hlam]
                                          · linarith only [h14511, h14613, hlam]
                                        · linarith only [h14612, hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        rcases p14573_3 (m.d 0 2) (by simp) with h14619 | h14619
                                        · rcases p14573_3 (m.d 1 2) (by simp) with h14620 | h14620
                                          · rcases p14573_3 (m.d 2 3) (by simp) with h14621 | h14621
                                            · linarith only [h14399, h14621, hlam]
                                            · linarith only [h14518, h14621, hlam]
                                          · linarith only [h14512, h14620, hlam]
                                        · linarith only [h14619, hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h0, h14396, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p14523_1, p14573_1]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        rcases p14573_3 (m.d 0 2) (by simp) with h14628 | h14628
                                        · linarith only [h0, h14628, hlam]
                                        · linarith only [h14399, h14628, hlam]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h0, h14396, h14397, h14404, h14511, hlam, p14523_1, p14573_2]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h0, h14396, h14398, h14512, hlam, p14523_1, p14573_2]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14399, hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14510, hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h0, h14396, h14510, h14517, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14573_1]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h0, h14396, h14510, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p14573_1]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14400, hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14511, hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14517, hlam, p14573_1]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14519, hlam, p14573_1]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14401, hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14512, hlam, p14573_0]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14518, hlam, p14573_1]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [h14401, h14517, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p14523_1, p14573_1]
                                      · have p14573_0 := h14573c.1
                                        have p14573_1 := h14573c.2.1
                                        have p14573_2 := h14573c.2.2.1
                                        have p14573_3 := h14573c.2.2.2
                                        linarith only [hlam, p14573_0]
                                · linarith only [h14403, h14568, hlam]
                              · linarith only [h14401, h14567, hlam]
                            · linarith only [h14398, h14566, hlam]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h14397, hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h14400, hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h14402, hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h14404, hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h14398, hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h14401, hlam, p14523_1]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [h14403, hlam, p14523_0]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            rcases p14523_3 (m.d 0 1) (by simp) with h14659 | h14659
                            · rcases p14523_3 (m.d 0 2) (by simp) with h14660 | h14660
                              · rcases p14523_3 (m.d 0 3) (by simp) with h14661 | h14661
                                · rcases p14523_3 (m.d 0 4) (by simp) with h14662 | h14662
                                  · linarith only [h14404, h14662, hlam]
                                  · rcases p14523_3 (m.d 0 5) (by simp) with h14664 | h14664
                                    · rcases h2bigk with h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c | h14665c
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h0, hlam, p14665_1]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        rcases p14665_3 (m.d 0 2) (by simp) with h14668 | h14668
                                        · rcases p14665_3 (m.d 1 2) (by simp) with h14669 | h14669
                                          · rcases p14665_3 (m.d 2 3) (by simp) with h14670 | h14670
                                            · linarith only [h14670, hlam, p14665_0]
                                            · rcases p14665_3 (m.d 2 4) (by simp) with h14672 | h14672
                                              · linarith only [h14400, h14672, hlam]
                                              · rcases p14665_3 (m.d 2 5) (by simp) with h14674 | h14674
                                                · linarith only [h14401, h14674, hlam]
                                                · rcases h3bigk with h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c | h14676c
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h0, h14396, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h0, h14396, h14518, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h0, h14396, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h0, h14396, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14396, hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14518, h14521, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h0, h14396, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h0, h14396, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14399, hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14510, hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p14665_1, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h0, h14521, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14665_1, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14402, hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14513, hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14517, hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14521, hlam, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14403, hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14514, hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h14518, hlam, p14676_0]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [h0, h14396, h14403, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14676_1]
                                                  · have p14676_0 := h14676c.1
                                                    have p14676_1 := h14676c.2.1
                                                    have p14676_2 := h14676c.2.2.1
                                                    have p14676_3 := h14676c.2.2.2
                                                    linarith only [hlam, p14676_0]
                                          · linarith only [h14510, h14669, hlam]
                                        · linarith only [h14668, hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        rcases p14665_3 (m.d 0 2) (by simp) with h14704 | h14704
                                        · rcases p14665_3 (m.d 1 2) (by simp) with h14705 | h14705
                                          · rcases p14665_3 (m.d 2 3) (by simp) with h14706 | h14706
                                            · linarith only [h14399, h14706, hlam]
                                            · linarith only [h14517, h14706, hlam]
                                          · linarith only [h14511, h14705, hlam]
                                        · linarith only [h14704, hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        rcases p14665_3 (m.d 0 2) (by simp) with h14711 | h14711
                                        · rcases p14665_3 (m.d 1 2) (by simp) with h14712 | h14712
                                          · rcases p14665_3 (m.d 2 3) (by simp) with h14713 | h14713
                                            · linarith only [h14399, h14713, hlam]
                                            · linarith only [h14518, h14713, hlam]
                                          · linarith only [h14512, h14712, hlam]
                                        · linarith only [h14711, hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h0, h14397, h14398, h14511, h14517, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14523_1, p14665_1]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        rcases p14665_3 (m.d 0 2) (by simp) with h14720 | h14720
                                        · linarith only [h0, h14720, hlam]
                                        · linarith only [h14399, h14720, hlam]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h0, h14396, h14397, h14403, h14511, hlam, p14523_1, p14665_2]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        rcases p14665_3 (m.d 0 2) (by simp) with h14724 | h14724
                                        · linarith only [h0, h14724, hlam]
                                        · linarith only [h14401, h14724, hlam]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h14399, hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h14510, hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h0, h14396, h14510, h14517, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14665_1]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h0, h14396, h14510, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p14665_1]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h14400, hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h14511, hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h14517, hlam, p14665_1]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h14519, hlam, p14665_1]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h14401, hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h14512, hlam, p14665_0]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h14518, hlam, p14665_1]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [h0, h14396, h14512, h14514, h14517, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14665_1]
                                      · have p14665_0 := h14665c.1
                                        have p14665_1 := h14665c.2.1
                                        have p14665_2 := h14665c.2.2.1
                                        have p14665_3 := h14665c.2.2.2
                                        linarith only [hlam, p14665_0]
                                    · linarith only [h14404, h14664, hlam]
                                · linarith only [h14402, h14661, hlam]
                              · linarith only [h14400, h14660, hlam]
                            · linarith only [h14397, h14659, hlam]
                          · have p14523_0 := h14523c.1
                            have p14523_1 := h14523c.2.1
                            have p14523_2 := h14523c.2.2.1
                            have p14523_3 := h14523c.2.2.2
                            linarith only [hlam, p14523_0]
                    · linarith only [h0, h14396, h14514, h14518, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h14396, h14513, h14517, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h14396, h14403, h14513, h14514, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14750 | h14750
              · linarith only [h0, h14396, h14402, h14513, h14750, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14752 | h14752
                · linarith only [h0, h14397, h14404, h14752, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14754 | h14754
                  · linarith only [h14510, h14513, h14754, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14756 | h14756
                    · linarith only [h0, h14396, h14402, h14510, h14512, h14513, h14750, h14756, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14758 | h14758
                      · linarith only [h14397, h14402, h14404, h14510, h14511, h14513, h14758, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14760 | h14760
                        · linarith only [h14402, h14404, h14760, hlam]
                        · rcases h0bigk with h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c | h14762c
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h0, hlam, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h0, h14403, h14750, h14752, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h0, h14402, h14510, h14513, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h0, h14402, h14404, h14510, h14513, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h0, h14396, h14402, h14510, h14513, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h0, h14402, h14510, h14513, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            rcases p14762_3 (m.d 0 1) (by simp) with h14771 | h14771
                            · linarith only [h0, h14771, hlam]
                            · linarith only [h14397, h14771, hlam]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            rcases p14762_3 (m.d 0 1) (by simp) with h14774 | h14774
                            · linarith only [h0, h14774, hlam]
                            · linarith only [h14398, h14774, hlam]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h14396, hlam, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h14399, hlam, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h0, h14396, h14402, h14510, h14513, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h0, h14396, h14402, h14404, h14510, h14513, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h14397, hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h14400, hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h14402, hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h14404, hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h14398, hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h14401, hlam, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h14403, hlam, p14762_0]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [h0, h14398, h14402, h14510, h14513, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14762_1]
                          · have p14762_0 := h14762c.1
                            have p14762_1 := h14762c.2.1
                            have p14762_2 := h14762c.2.2.1
                            have p14762_3 := h14762c.2.2.2
                            linarith only [hlam, p14762_0]
          · linarith only [h0, h14401, h14512, hlam]
        · linarith only [h0, h14400, h14511, hlam]
      · linarith only [h0, h14399, h14510, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h14795 | h14795
    · linarith only [h14402, h14403, h14795, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h14797 | h14797
      · rcases m.htr 1 2 4 (by decide) (by decide) with h14798 | h14798
        · rcases m.htr 1 2 5 (by decide) (by decide) with h14799 | h14799
          · rcases m.htr 1 3 4 (by decide) (by decide) with h14800 | h14800
            · rcases m.htr 1 3 5 (by decide) (by decide) with h14801 | h14801
              · linarith only [h0, h14396, h14403, h14801, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h14803 | h14803
                · linarith only [h0, h14398, h14795, h14800, h14801, h14803, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h14805 | h14805
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h14806 | h14806
                    · linarith only [h14396, h14403, h14797, h14806, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h14808 | h14808
                      · linarith only [h0, h14397, h14402, h14403, h14795, h14798, h14808, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h14810 | h14810
                        · linarith only [h14396, h14397, h14403, h14795, h14797, h14798, h14805, h14810, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                        · rcases h0bigk with h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c | h14812c
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [hlam, p14812_0]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h0, hlam, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h0, h14402, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            rcases p14812_3 (m.d 0 1) (by simp) with h14816 | h14816
                            · rcases p14812_3 (m.d 0 2) (by simp) with h14817 | h14817
                              · rcases p14812_3 (m.d 0 3) (by simp) with h14818 | h14818
                                · linarith only [h14396, h14818, hlam]
                                · linarith only [h14402, h14818, hlam]
                              · linarith only [h14400, h14817, hlam]
                            · linarith only [h14397, h14816, hlam]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h0, h14396, h14403, h14797, h14805, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h0, h14396, h14797, h14805, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [hlam, p14812_0]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            rcases p14812_3 (m.d 0 1) (by simp) with h14826 | h14826
                            · linarith only [h0, h14826, hlam]
                            · linarith only [h14396, h14826, hlam]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            rcases p14812_3 (m.d 0 1) (by simp) with h14829 | h14829
                            · linarith only [h0, h14829, hlam]
                            · linarith only [h14397, h14829, hlam]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            rcases p14812_3 (m.d 0 1) (by simp) with h14832 | h14832
                            · linarith only [h0, h14832, hlam]
                            · linarith only [h14398, h14832, hlam]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14396, hlam, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14399, hlam, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [hlam, p14812_0]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14397, h14403, h14798, h14805, h14810, hc34, hc45, hlam, hphi, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14403, hlam, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14397, hlam, p14812_0]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14400, hlam, p14812_0]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14402, hlam, p14812_0]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [hlam, p14812_0]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14795, hlam, p14812_0]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14398, hlam, p14812_0]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h14401, hlam, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [h0, h14396, h14398, h14797, h14805, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p14812_1]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            rcases p14812_3 (m.d 0 1) (by simp) with h14848 | h14848
                            · rcases p14812_3 (m.d 0 2) (by simp) with h14849 | h14849
                              · rcases p14812_3 (m.d 0 3) (by simp) with h14850 | h14850
                                · linarith only [h14403, h14850, hlam]
                                · linarith only [h14402, h14850, hlam]
                              · linarith only [h14400, h14849, hlam]
                            · linarith only [h14397, h14848, hlam]
                          · have p14812_0 := h14812c.1
                            have p14812_1 := h14812c.2.1
                            have p14812_2 := h14812c.2.2.1
                            have p14812_3 := h14812c.2.2.2
                            linarith only [hlam, p14812_0]
                  · linarith only [h14402, h14403, h14805, hc23, hc35, hlam, hphi]
            · linarith only [h14402, h14403, h14800, hc13, hc35, hlam, hphi]
          · linarith only [h0, h14401, h14799, hlam]
        · linarith only [h0, h14400, h14798, hlam]
      · linarith only [h0, h14399, h14797, hlam]

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x0_x0_x0_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h14398 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h14399 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h14400 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h14401 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h14402 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h14861 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h14862 | h14862
  · rcases m.htr 1 2 3 (by decide) (by decide) with h14863 | h14863
    · rcases m.htr 1 2 4 (by decide) (by decide) with h14864 | h14864
      · rcases m.htr 1 2 5 (by decide) (by decide) with h14865 | h14865
        · rcases m.htr 1 3 4 (by decide) (by decide) with h14866 | h14866
          · linarith only [h0, h14396, h14402, h14866, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h14868 | h14868
            · rcases m.htr 1 4 5 (by decide) (by decide) with h14869 | h14869
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14870 | h14870
                · linarith only [h14396, h14402, h14863, h14870, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h14872 | h14872
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h14873 | h14873
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h14874 | h14874
                      · rcases h0bigk with h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c | h14875c
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [hlam, p14875_0]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h0, hlam, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h0, h14396, h14863, h14872, h14874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h0, h14396, h14402, h14863, h14872, h14874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          rcases p14875_3 (m.d 0 1) (by simp) with h14880 | h14880
                          · rcases p14875_3 (m.d 0 2) (by simp) with h14881 | h14881
                            · rcases p14875_3 (m.d 0 3) (by simp) with h14882 | h14882
                              · linarith only [h14396, h14882, hlam]
                              · linarith only [h14861, h14882, hlam]
                            · linarith only [h14401, h14881, hlam]
                          · linarith only [h14398, h14880, hlam]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h0, h14396, h14863, h14872, h14874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [hlam, p14875_0]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          rcases p14875_3 (m.d 0 1) (by simp) with h14889 | h14889
                          · linarith only [h0, h14889, hlam]
                          · linarith only [h14396, h14889, hlam]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          rcases p14875_3 (m.d 0 1) (by simp) with h14892 | h14892
                          · linarith only [h0, h14892, hlam]
                          · linarith only [h14397, h14892, hlam]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          rcases p14875_3 (m.d 0 1) (by simp) with h14895 | h14895
                          · linarith only [h0, h14895, hlam]
                          · linarith only [h14398, h14895, hlam]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h14396, hlam, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h14399, hlam, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [hlam, p14875_0]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h14402, hlam, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          rcases p14875_3 (m.d 0 1) (by simp) with h14902 | h14902
                          · rcases p14875_3 (m.d 0 2) (by simp) with h14903 | h14903
                            · rcases p14875_3 (m.d 0 3) (by simp) with h14904 | h14904
                              · rcases p14875_3 (m.d 0 4) (by simp) with h14905 | h14905
                                · rcases p14875_3 (m.d 0 5) (by simp) with h14906 | h14906
                                  · linarith only [h14861, h14906, hlam]
                                  · rcases h2bigk with h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c | h14908c
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h0, hlam, p14908_1]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      rcases p14908_3 (m.d 0 2) (by simp) with h14911 | h14911
                                      · rcases p14908_3 (m.d 1 2) (by simp) with h14912 | h14912
                                        · rcases p14908_3 (m.d 2 3) (by simp) with h14913 | h14913
                                          · linarith only [h14913, hlam, p14908_0]
                                          · rcases p14908_3 (m.d 2 4) (by simp) with h14915 | h14915
                                            · linarith only [h14400, h14915, hlam]
                                            · linarith only [h14870, h14915, hlam]
                                        · linarith only [h14863, h14912, hlam]
                                      · linarith only [h14911, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      rcases p14908_3 (m.d 0 2) (by simp) with h14920 | h14920
                                      · rcases p14908_3 (m.d 1 2) (by simp) with h14921 | h14921
                                        · rcases p14908_3 (m.d 2 3) (by simp) with h14922 | h14922
                                          · linarith only [h14399, h14922, hlam]
                                          · rcases p14908_3 (m.d 2 4) (by simp) with h14924 | h14924
                                            · linarith only [h14924, hlam, p14908_0]
                                            · rcases p14908_3 (m.d 2 5) (by simp) with h14926 | h14926
                                              · linarith only [h14401, h14926, hlam]
                                              · rcases h3bigk with h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c | h14928c
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14402, h14863, h14872, h14874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14928_1]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14402, h14872, h14874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14928_1]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14402, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14402, h14874, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14928_1]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14396, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14872, h14874, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p14928_1]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14866, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h0, h14397, h14866, h14874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14928_1]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14399, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14863, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14870, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14399, h14874, hc02, hc45, hlam, hphi, ht0b, ht5b, p14928_1]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [hc03, hc34, hlam, hphi, p14928_1]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [hc13, hc34, hlam, hphi, p14928_1]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [hc23, hc34, hlam, hphi, p14928_1]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  rcases p14928_3 (m.d 0 3) (by simp) with h14948 | h14948
                                                  · linarith only [h14402, h14948, hlam]
                                                  · linarith only [h14861, h14948, hlam]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14861, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14868, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14872, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [h14874, hlam, p14928_0]
                                                · have p14928_0 := h14928c.1
                                                  have p14928_1 := h14928c.2.1
                                                  have p14928_2 := h14928c.2.2.1
                                                  have p14928_3 := h14928c.2.2.2
                                                  linarith only [hlam, p14928_0]
                                        · linarith only [h14864, h14921, hlam]
                                      · linarith only [h14920, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      rcases p14908_3 (m.d 0 2) (by simp) with h14958 | h14958
                                      · rcases p14908_3 (m.d 1 2) (by simp) with h14959 | h14959
                                        · rcases p14908_3 (m.d 2 3) (by simp) with h14960 | h14960
                                          · linarith only [h14399, h14960, hlam]
                                          · linarith only [h14872, h14960, hlam]
                                        · linarith only [h14865, h14959, hlam]
                                      · linarith only [h14958, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h0, h14396, h14863, h14872, h14874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14908_1]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      rcases p14908_3 (m.d 0 2) (by simp) with h14967 | h14967
                                      · linarith only [h0, h14967, hlam]
                                      · linarith only [h14399, h14967, hlam]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      rcases p14908_3 (m.d 0 2) (by simp) with h14970 | h14970
                                      · linarith only [h0, h14970, hlam]
                                      · linarith only [h14400, h14970, hlam]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h0, h14397, h14398, h14402, h14865, hlam, p14875_1, p14908_2]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h14399, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h14863, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h14870, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h0, h14396, h14863, h14872, h14874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14908_1]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h14400, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h14864, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h0, h14397, h14864, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14908_1]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h0, h14397, h14864, h14872, h14874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14908_1]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h14401, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h14865, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h14872, hlam, p14908_1]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [h14873, hlam, p14908_0]
                                    · have p14908_0 := h14908c.1
                                      have p14908_1 := h14908c.2.1
                                      have p14908_2 := h14908c.2.2.1
                                      have p14908_3 := h14908c.2.2.2
                                      linarith only [hlam, p14908_0]
                                · linarith only [h14862, h14905, hlam]
                              · linarith only [h14861, h14904, hlam]
                            · linarith only [h14401, h14903, hlam]
                          · linarith only [h14398, h14902, hlam]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h14397, hlam, p14875_0]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h14400, hlam, p14875_0]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h0, h14397, h14399, h14872, h14874, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [hlam, p14875_0]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          rcases p14875_3 (m.d 0 1) (by simp) with h14997 | h14997
                          · rcases p14875_3 (m.d 0 2) (by simp) with h14998 | h14998
                            · rcases p14875_3 (m.d 0 3) (by simp) with h14999 | h14999
                              · linarith only [h14402, h14999, hlam]
                              · linarith only [h14861, h14999, hlam]
                            · linarith only [h14401, h14998, hlam]
                          · linarith only [h14398, h14997, hlam]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h14398, hlam, p14875_0]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h14401, hlam, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h14861, hlam, p14875_0]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [h14862, hlam, p14875_1]
                        · have p14875_0 := h14875c.1
                          have p14875_1 := h14875c.2.1
                          have p14875_2 := h14875c.2.2.1
                          have p14875_3 := h14875c.2.2.2
                          linarith only [hlam, p14875_0]
                      · linarith only [h14402, h14862, h14874, hlam]
                    · linarith only [h0, h14397, h14869, h14873, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h14402, h14861, h14872, hc23, hc34, hlam, hphi]
              · linarith only [h0, h14397, h14862, h14866, h14868, h14869, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h14402, h14861, h14863, h14868, hc23, hc34, hlam, hphi]
        · linarith only [h0, h14401, h14865, hlam]
      · linarith only [h0, h14400, h14864, hlam]
    · linarith only [h0, h14399, h14863, hlam]
  · linarith only [h14402, h14861, h14862, hlam]

end R2N4
