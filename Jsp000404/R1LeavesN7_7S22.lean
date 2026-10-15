import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S21

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8040000 in
set_option maxHeartbeats 8040000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s15_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h12233 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h14944 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  rcases m.htr 0 2 5 (by decide) (by decide) with h15376 | h15376
  · rcases m.htr 0 3 4 (by decide) (by decide) with h15377 | h15377
    · rcases m.htr 0 3 5 (by decide) (by decide) with h15378 | h15378
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15379 | h15379
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15380 | h15380
          · linarith only [h12233, h15376, h15380, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15382 | h15382
            · linarith only [h14944, h15376, h15380, h15382, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15384 | h15384
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15385 | h15385
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15386 | h15386
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15387 | h15387
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15388 | h15388
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15389 | h15389
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15390 | h15390
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15391 | h15391
                            · rcases h1bigk with h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c | h15392c
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h0, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h10472, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h11379, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h12013, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15382, h15388, hc01, hc23, hlam, hphi, ht12, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15380, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15382, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15382, h15388, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p15392_1, u5ehi1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                rcases p15392_3 (m.d 0 1) (by simp) with h15403 | h15403
                                · linarith only [h15403, hlam, p15392_0]
                                · rcases p15392_3 (m.d 1 2) (by simp) with h15405 | h15405
                                  · linarith only [h15380, h15405, hlam]
                                  · linarith only [h0, h15405, hlam]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h0, h15376, h15380, h15382, h15389, h15391, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p15392_1, u5ehi4]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h12013, h15380, hc01, hc23, hlam, hphi, ht12, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                rcases p15392_3 (m.d 0 1) (by simp) with h15412 | h15412
                                · linarith only [h15412, hlam, p15392_0]
                                · rcases p15392_3 (m.d 1 2) (by simp) with h15414 | h15414
                                  · linarith only [h15382, h15414, hlam]
                                  · linarith only [h0, h15414, hlam]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h0, h15376, h15389, h15391, hc14, hlam, hphi, ht01, ht0b, ht5b, p15392_1, u5ehi4]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15385, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h12013, h15382, h15388, hc01, hc23, hlam, hphi, ht12, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15380, h15384, hc01, hc23, hlam, hphi, ht12, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15384, hlam, p15392_1]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15386, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [h15387, hlam, p15392_0]
                              · have p15392_0 := h15392c.1
                                have p15392_1 := h15392c.2.1
                                have p15392_2 := h15392c.2.2.1
                                have p15392_3 := h15392c.2.2.2
                                linarith only [hlam, p15392_0]
                            · rcases h1bigk with h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c | h15426c
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h0, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h10472, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11379, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h12013, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15382, h15388, hc01, hc23, hlam, hphi, ht12, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15380, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15382, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15382, h15388, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p15426_1, u5ehi1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                rcases p15426_3 (m.d 0 1) (by simp) with h15437 | h15437
                                · linarith only [h15437, hlam, p15426_0]
                                · rcases p15426_3 (m.d 1 2) (by simp) with h15439 | h15439
                                  · linarith only [h15380, h15439, hlam]
                                  · linarith only [h0, h15439, hlam]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h0, h15380, hc01, hc23, hlam, hphi, ht12, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h11379, h15380, hc01, hc23, hlam, hphi, ht12, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h12013, h15380, hc01, hc23, hlam, hphi, ht12, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                rcases p15426_3 (m.d 0 1) (by simp) with h15446 | h15446
                                · linarith only [h15446, hlam, p15426_0]
                                · rcases p15426_3 (m.d 1 2) (by simp) with h15448 | h15448
                                  · linarith only [h15382, h15448, hlam]
                                  · linarith only [h0, h15448, hlam]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h0, h15376, hc14, hlam, hphi, ht01, ht0b, ht5b, p15426_1, u5ehi2]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15385, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h12013, h15382, h15388, hc01, hc23, hlam, hphi, ht12, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15380, h15384, hc01, hc23, hlam, hphi, ht12, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15384, hlam, p15426_1]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15386, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [h15387, hlam, p15426_0]
                              · have p15426_0 := h15426c.1
                                have p15426_1 := h15426c.2.1
                                have p15426_2 := h15426c.2.2.1
                                have p15426_3 := h15426c.2.2.2
                                linarith only [hlam, p15426_0]
                          · linarith only [h0, h15382, h15390, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h15376, h15382, h15388, h15389, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h12233, h15376, h15388, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h10472, h15377, h15379, h15382, h15387, hc01, hc13, hlam, hphi]
                  · linarith only [h10472, h12233, h15376, h15378, h15386, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10472, h15377, h15385, hlam]
              · linarith only [h0, h15376, h15384, hlam]
        · linarith only [h14944, h15376, h15379, hlam]
      · linarith only [h14944, h15376, h15377, h15378, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h15469 | h15469
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15470 | h15470
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15471 | h15471
          · linarith only [h12233, h15376, h15471, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15473 | h15473
            · linarith only [h14944, h15376, h15473, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15475 | h15475
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15476 | h15476
                · linarith only [h15377, h15469, h15476, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15478 | h15478
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15479 | h15479
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15480 | h15480
                      · linarith only [h0, h15471, h15476, h15480, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h12233, h15376, h15480, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h0, h15376, h15470, h15471, h15476, h15479, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h0, h15376, h15469, h15471, h15478, hc03, hlam, hphi, ht0b, ht5b, u5ehi2]
              · linarith only [h0, h15376, h15475, hlam]
        · linarith only [h12233, h15376, h15377, h15470, hlam]
      · linarith only [h12233, h15376, h15469, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h15488 | h15488
    · rcases m.htr 0 3 5 (by decide) (by decide) with h15489 | h15489
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15490 | h15490
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15491 | h15491
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15492 | h15492
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15493 | h15493
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15494 | h15494
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15495 | h15495
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15496 | h15496
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15497 | h15497
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15498 | h15498
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15499 | h15499
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15500 | h15500
                            · linarith only [h12233, h15488, h15491, h15500, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                            · rcases h1bigk with h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c | h15502c
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h0, hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h10472, hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h11379, hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h12013, hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                rcases p15502_3 (m.d 0 1) (by simp) with h15508 | h15508
                                · linarith only [h15508, hlam, p15502_0]
                                · rcases p15502_3 (m.d 1 2) (by simp) with h15510 | h15510
                                  · rcases p15502_3 (m.d 1 3) (by simp) with h15511 | h15511
                                    · linarith only [h15491, h15511, hlam]
                                    · linarith only [h10472, h15511, hlam]
                                  · linarith only [h15510, hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h10472, hc01, hc12, hlam, hphi, p15502_1]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h11379, hc01, hc12, hlam, hphi, p15502_1]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h0, h15376, h15493, hc01, hc12, hlam, hphi, p15502_1]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                rcases p15502_3 (m.d 0 1) (by simp) with h15519 | h15519
                                · linarith only [h15519, hlam, p15502_0]
                                · rcases p15502_3 (m.d 1 2) (by simp) with h15521 | h15521
                                  · rcases p15502_3 (m.d 1 3) (by simp) with h15522 | h15522
                                    · rcases p15502_3 (m.d 1 4) (by simp) with h15523 | h15523
                                      · linarith only [h15494, h15523, hlam]
                                      · linarith only [h11379, h15523, hlam]
                                    · linarith only [h15522, hlam, p15502_0]
                                  · linarith only [h0, h15521, hlam]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h15491, hlam, p15502_1]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h11379, hc01, hc13, hlam, hphi, p15502_1]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h12013, h15491, hc01, hc12, hlam, hphi, p15502_1]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                rcases p15502_3 (m.d 0 1) (by simp) with h15532 | h15532
                                · linarith only [h15532, hlam, p15502_0]
                                · rcases p15502_3 (m.d 1 2) (by simp) with h15534 | h15534
                                  · rcases p15502_3 (m.d 1 3) (by simp) with h15535 | h15535
                                    · rcases p15502_3 (m.d 1 4) (by simp) with h15536 | h15536
                                      · rcases p15502_3 (m.d 1 5) (by simp) with h15537 | h15537
                                        · linarith only [h15496, h15537, hlam]
                                        · linarith only [h12013, h15537, hlam]
                                      · linarith only [h15536, hlam, p15502_0]
                                    · linarith only [h10472, h15535, hlam]
                                  · linarith only [h0, h15534, hlam]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h15492, hlam, p15502_1]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h15494, hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h0, h15376, h15493, hc01, hc14, hlam, hphi, p15502_1]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                rcases p15502_3 (m.d 0 1) (by simp) with h15547 | h15547
                                · linarith only [h15547, hlam, p15502_0]
                                · rcases p15502_3 (m.d 1 2) (by simp) with h15549 | h15549
                                  · rcases p15502_3 (m.d 1 3) (by simp) with h15550 | h15550
                                    · rcases p15502_3 (m.d 1 4) (by simp) with h15551 | h15551
                                      · rcases p15502_3 (m.d 1 5) (by simp) with h15552 | h15552
                                        · rcases h1emax with h15553 | h15553 | h15553 | h15553 | h15553
                                          · rcases h3bigk with h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c | h15554c
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h10472, hlam, p15554_1]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h12233, hlam, p15554_1]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              rcases p15554_3 (m.d 0 3) (by simp) with h15558 | h15558
                                              · rcases p15554_3 (m.d 1 3) (by simp) with h15559 | h15559
                                                · rcases p15554_3 (m.d 2 3) (by simp) with h15560 | h15560
                                                  · rcases p15554_3 (m.d 3 4) (by simp) with h15561 | h15561
                                                    · linarith only [h15561, hlam, p15554_0]
                                                    · rcases p15554_3 (m.d 3 5) (by simp) with h15563 | h15563
                                                      · linarith only [h15489, h15563, hlam]
                                                      · linarith only [h15500, h15563, hlam]
                                                  · linarith only [h15497, h15560, hlam]
                                                · linarith only [h15494, h15559, hlam]
                                              · linarith only [h15558, hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h12233, h15491, hc12, hlam, hphi, ht01, ht0b, ht5b, p15554_1, u5ehi3]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15488, h15490, h15491, h15500, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15554_1]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h0, h12233, h15491, hc01, hc12, hlam, hphi, p15554_1]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              rcases p15554_3 (m.d 0 3) (by simp) with h15573 | h15573
                                              · linarith only [h10472, h15573, hlam]
                                              · linarith only [h15488, h15573, hlam]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              rcases p15554_3 (m.d 0 3) (by simp) with h15576 | h15576
                                              · linarith only [h10472, h15576, hlam]
                                              · linarith only [h15489, h15576, hlam]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15488, h15490, h15500, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15554_1]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15491, hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              rcases p15554_3 (m.d 0 3) (by simp) with h15582 | h15582
                                              · linarith only [h12233, h15582, hlam]
                                              · linarith only [h15488, h15582, hlam]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15491, hc12, hlam, hphi, ht01, ht0b, ht5b, p15554_1, u5ehi3]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15488, hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15494, hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15497, hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15500, hlam, p15554_1]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15489, hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15495, hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h15498, hlam, p15554_0]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [h12233, h15489, h15491, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p15554_1]
                                            · have p15554_0 := h15554c.1
                                              have p15554_1 := h15554c.2.1
                                              have p15554_2 := h15554c.2.2.1
                                              have p15554_3 := h15554c.2.2.2
                                              linarith only [hlam, p15554_0]
                                          · linarith only [h0, h15553, hc01, hlam]
                                          · linarith only [h15494, h15496, h15553, hc01, hlam, p15502_1]
                                          · linarith only [h15496, h15553, hc01, hlam, p15502_1]
                                          · linarith only [h15553, hc01, hlam, p15502_1]
                                        · linarith only [h15552, hlam, p15502_0]
                                      · linarith only [h11379, h15551, hlam]
                                    · linarith only [h10472, h15550, hlam]
                                  · linarith only [h0, h15549, hlam]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h15493, hlam, p15502_1]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h15495, hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [h15496, hlam, p15502_0]
                              · have p15502_0 := h15502c.1
                                have p15502_1 := h15502c.2.1
                                have p15502_2 := h15502c.2.2.1
                                have p15502_3 := h15502c.2.2.2
                                linarith only [hlam, p15502_0]
                          · linarith only [h14944, h15490, h15499, hlam]
                        · linarith only [h12233, h15489, h15498, hlam]
                      · linarith only [h12233, h15488, h15497, hlam]
                    · linarith only [h11379, h12233, h15488, h15490, h15491, h15496, hc01, hc12, hlam, hphi]
                  · linarith only [h12233, h15489, h15491, h15495, hlam]
                · linarith only [h12233, h15488, h15491, h15494, hlam]
              · linarith only [h12233, h15489, h15491, h15493, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h12233, h15488, h15490, h15491, h15492, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15616 | h15616
            · linarith only [h0, h14944, h15491, h15616, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15618 | h15618
              · linarith only [h0, h15376, h15491, h15618, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15620 | h15620
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15621 | h15621
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15622 | h15622
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15623 | h15623
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15624 | h15624
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15625 | h15625
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15626 | h15626
                            · rcases h1bigk with h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c | h15627c
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h0, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h10472, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h11379, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h12013, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h15618, h15623, h15625, hc01, hc23, hlam, hphi, ht12, p15627_1]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h15491, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h15616, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h15618, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                rcases p15627_3 (m.d 0 1) (by simp) with h15638 | h15638
                                · linarith only [h15638, hlam, p15627_0]
                                · rcases p15627_3 (m.d 1 2) (by simp) with h15640 | h15640
                                  · linarith only [h15491, h15640, hlam]
                                  · linarith only [h0, h15640, hlam]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p15627_1]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h11379, h15488, h15491, h15626, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p15627_1, u5ehi4]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h0, h15491, h15618, hc01, hc23, hlam, hphi, ht12, p15627_1]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                rcases p15627_3 (m.d 0 1) (by simp) with h15647 | h15647
                                · linarith only [h15647, hlam, p15627_0]
                                · rcases p15627_3 (m.d 1 2) (by simp) with h15649 | h15649
                                  · linarith only [h15616, h15649, hlam]
                                  · linarith only [h0, h15649, hlam]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p15627_1]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h15620, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h0, h15616, h15618, h15623, hc01, hc23, hlam, hphi, ht12, p15627_1]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                rcases p15627_3 (m.d 0 1) (by simp) with h15656 | h15656
                                · linarith only [h15656, hlam, p15627_0]
                                · rcases p15627_3 (m.d 1 2) (by simp) with h15658 | h15658
                                  · linarith only [h15618, h15658, hlam]
                                  · linarith only [h0, h15658, hlam]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p15627_1]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h15621, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [h15622, hlam, p15627_0]
                              · have p15627_0 := h15627c.1
                                have p15627_1 := h15627c.2.1
                                have p15627_2 := h15627c.2.2.1
                                have p15627_3 := h15627c.2.2.2
                                linarith only [hlam, p15627_0]
                            · rcases h1bigk with h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c | h15665c
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h0, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h10472, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h11379, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h12013, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h15491, hc01, hc23, hlam, hphi, ht12, p15665_1]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h15491, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h15616, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h15618, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                rcases p15665_3 (m.d 0 1) (by simp) with h15676 | h15676
                                · linarith only [h15676, hlam, p15665_0]
                                · rcases p15665_3 (m.d 1 2) (by simp) with h15678 | h15678
                                  · linarith only [h15491, h15678, hlam]
                                  · linarith only [h0, h15678, hlam]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h0, h15491, hc01, hc23, hlam, hphi, ht12, p15665_1]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h11379, h15491, hc01, hc23, hlam, hphi, ht12, p15665_1]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h12013, h15491, hc01, hc23, hlam, hphi, ht12, p15665_1]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                rcases p15665_3 (m.d 0 1) (by simp) with h15685 | h15685
                                · linarith only [h15685, hlam, p15665_0]
                                · rcases p15665_3 (m.d 1 2) (by simp) with h15687 | h15687
                                  · linarith only [h15616, h15687, hlam]
                                  · linarith only [h0, h15687, hlam]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p15665_1]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h15620, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h12013, h15616, h15623, hc01, hc23, hlam, hphi, ht12, p15665_1]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                rcases p15665_3 (m.d 0 1) (by simp) with h15694 | h15694
                                · linarith only [h15694, hlam, p15665_0]
                                · rcases p15665_3 (m.d 1 2) (by simp) with h15696 | h15696
                                  · linarith only [h15618, h15696, hlam]
                                  · linarith only [h0, h15696, hlam]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p15665_1]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h15621, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [h15622, hlam, p15665_0]
                              · have p15665_0 := h15665c.1
                                have p15665_1 := h15665c.2.1
                                have p15665_2 := h15665c.2.2.1
                                have p15665_3 := h15665c.2.2.2
                                linarith only [hlam, p15665_0]
                          · linarith only [h11379, h15490, h15616, h15625, hlam]
                        · linarith only [h10472, h15489, h15491, h15624, hlam]
                      · linarith only [h0, h15491, h15623, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h11379, h15490, h15622, hlam]
                  · linarith only [h10472, h15489, h15621, hlam]
                · linarith only [h10472, h15488, h15620, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15709 | h15709
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15710 | h15710
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15711 | h15711
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15712 | h15712
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15713 | h15713
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15714 | h15714
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15715 | h15715
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15716 | h15716
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15717 | h15717
                          · linarith only [h11379, h15490, h15710, h15717, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h14944, h15709, h15712, h15714, h15717, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h10472, h12233, h15489, h15709, h15716, hc01, hc12, hlam, hphi]
                      · linarith only [h12233, h15488, h15715, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15722 | h15722
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15723 | h15723
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15724 | h15724
                          · linarith only [h15710, h15714, h15724, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15726 | h15726
                            · linarith only [h11379, h15488, h15714, h15726, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h1bigk with h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c | h15728c
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h0, hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h10472, hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h11379, hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h12013, hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                rcases p15728_3 (m.d 0 1) (by simp) with h15734 | h15734
                                · linarith only [h15734, hlam, p15728_0]
                                · rcases p15728_3 (m.d 1 2) (by simp) with h15736 | h15736
                                  · rcases p15728_3 (m.d 1 3) (by simp) with h15737 | h15737
                                    · linarith only [h15709, h15737, hlam]
                                    · linarith only [h10472, h15737, hlam]
                                  · linarith only [h15736, hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h10472, hc01, hc12, hlam, hphi, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h0, h14944, h15710, hc01, hc12, hlam, hphi, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h12013, hc01, hc12, hlam, hphi, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                rcases p15728_3 (m.d 0 1) (by simp) with h15745 | h15745
                                · linarith only [h15745, hlam, p15728_0]
                                · rcases p15728_3 (m.d 1 2) (by simp) with h15747 | h15747
                                  · rcases p15728_3 (m.d 1 3) (by simp) with h15748 | h15748
                                    · rcases p15728_3 (m.d 1 4) (by simp) with h15749 | h15749
                                      · linarith only [h15712, h15749, hlam]
                                      · linarith only [h11379, h15749, hlam]
                                    · linarith only [h15748, hlam, p15728_0]
                                  · linarith only [h0, h15747, hlam]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h15709, hlam, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h0, h14944, h15710, hc01, hc13, hlam, hphi, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h0, h14944, h15709, h15710, h15714, hc01, hc12, hlam, hphi, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h15714, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h15710, hlam, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h15712, hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h15714, hlam, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                rcases p15728_3 (m.d 0 1) (by simp) with h15763 | h15763
                                · linarith only [h15763, hlam, p15728_0]
                                · rcases p15728_3 (m.d 1 2) (by simp) with h15765 | h15765
                                  · rcases p15728_3 (m.d 1 3) (by simp) with h15766 | h15766
                                    · rcases p15728_3 (m.d 1 4) (by simp) with h15767 | h15767
                                      · linarith only [h15714, h15767, hlam]
                                      · linarith only [h11379, h15767, hlam]
                                    · linarith only [h10472, h15766, hlam]
                                  · linarith only [h0, h15765, hlam]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h15711, hlam, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h15713, hlam, p15728_0]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [h11379, hc01, hc15, hlam, hphi, p15728_1]
                              · have p15728_0 := h15728c.1
                                have p15728_1 := h15728c.2.1
                                have p15728_2 := h15728c.2.2.1
                                have p15728_3 := h15728c.2.2.2
                                linarith only [hlam, p15728_0]
                        · linarith only [h12233, h15489, h15723, hlam]
                      · linarith only [h12233, h15488, h15722, hlam]
                  · linarith only [h10472, h12233, h15489, h15709, h15713, hc01, hc12, hlam, hphi]
                · linarith only [h12233, h15488, h15709, h15712, hlam]
              · linarith only [h12233, h15489, h15709, h15711, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
            · linarith only [h0, h12233, h15709, h15710, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15782 | h15782
            · linarith only [h0, h14944, h15709, h15782, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15784 | h15784
              · linarith only [h0, h15376, h15709, h15784, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15786 | h15786
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15787 | h15787
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15788 | h15788
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15789 | h15789
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15790 | h15790
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15791 | h15791
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15792 | h15792
                            · linarith only [h15488, h15490, h15792, hlam]
                            · rcases h1bigk with h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c | h15794c
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h0, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h10472, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h11379, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h12013, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h15784, h15789, h15791, hc01, hc23, hlam, hphi, ht12, p15794_1]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h15709, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h15782, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h15784, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                rcases p15794_3 (m.d 0 1) (by simp) with h15805 | h15805
                                · linarith only [h15805, hlam, p15794_0]
                                · rcases p15794_3 (m.d 1 2) (by simp) with h15807 | h15807
                                  · linarith only [h15709, h15807, hlam]
                                  · linarith only [h0, h15807, hlam]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h0, h15709, hc01, hc23, hlam, hphi, ht12, p15794_1]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h11379, h15709, hc01, hc23, hlam, hphi, ht12, p15794_1]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h0, h15709, h15784, hc01, hc23, hlam, hphi, ht12, p15794_1]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                rcases p15794_3 (m.d 0 1) (by simp) with h15814 | h15814
                                · linarith only [h15814, hlam, p15794_0]
                                · rcases p15794_3 (m.d 1 2) (by simp) with h15816 | h15816
                                  · linarith only [h15782, h15816, hlam]
                                  · linarith only [h0, h15816, hlam]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p15794_1]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h15786, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h0, h14944, h15490, h15782, h15788, h15789, hc01, hc23, hlam, hphi, ht12, p15794_1]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                rcases p15794_3 (m.d 0 1) (by simp) with h15823 | h15823
                                · linarith only [h15823, hlam, p15794_0]
                                · rcases p15794_3 (m.d 1 2) (by simp) with h15825 | h15825
                                  · linarith only [h15784, h15825, hlam]
                                  · linarith only [h0, h15825, hlam]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p15794_1]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h15787, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [h15788, hlam, p15794_0]
                              · have p15794_0 := h15794c.1
                                have p15794_1 := h15794c.2.1
                                have p15794_2 := h15794c.2.2.1
                                have p15794_3 := h15794c.2.2.2
                                linarith only [hlam, p15794_0]
                          · linarith only [h0, h15782, h15791, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h10472, h15489, h15709, h15790, hlam]
                      · linarith only [h15488, h15490, h15709, h15786, h15788, h15789, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15835 | h15835
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15836 | h15836
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15837 | h15837
                          · linarith only [h11379, h15788, h15835, h15837, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h15782, h15837, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h10472, h12233, h15489, h15836, hc01, hc13, hlam, hphi]
                      · linarith only [h10472, h15488, h15709, h15835, hlam]
                  · linarith only [h10472, h15489, h15787, hlam]
                · linarith only [h10472, h15488, h15786, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15844 | h15844
        · linarith only [h15488, h15489, h15844, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15846 | h15846
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15847 | h15847
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15848 | h15848
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15849 | h15849
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15850 | h15850
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15851 | h15851
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15852 | h15852
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15853 | h15853
                        · linarith only [h15488, h15489, h15846, h15853, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h12233, h15846, h15850, h15853, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h10472, h12233, h15488, h15846, h15852, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15857 | h15857
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15858 | h15858
                        · linarith only [h10472, h15489, h15846, h15858, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h12233, h15846, h15850, h15858, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h10472, h12233, h15488, h15846, h15857, hc01, hc12, hlam, hphi]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15862 | h15862
                    · linarith only [h0, h14944, h15844, h15849, h15850, h15862, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15864 | h15864
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15865 | h15865
                        · linarith only [h15846, h15850, h15865, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15867 | h15867
                          · linarith only [h0, h14944, h15844, h15847, h15867, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15869 | h15869
                            · linarith only [h10472, h15488, h15850, h15862, h15869, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                            · rcases h1bigk with h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c | h15871c
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h0, hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h10472, hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h11379, hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h12013, hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                rcases p15871_3 (m.d 0 1) (by simp) with h15877 | h15877
                                · linarith only [h15877, hlam, p15871_0]
                                · rcases p15871_3 (m.d 1 2) (by simp) with h15879 | h15879
                                  · rcases p15871_3 (m.d 1 3) (by simp) with h15880 | h15880
                                    · linarith only [h15846, h15880, hlam]
                                    · linarith only [h10472, h15880, hlam]
                                  · linarith only [h15879, hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h10472, hc01, hc12, hlam, hphi, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h0, h14944, h15847, hc01, hc12, hlam, hphi, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h12013, hc01, hc12, hlam, hphi, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h15850, h15869, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h15846, hlam, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h0, h14944, h15847, hc01, hc13, hlam, hphi, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h15850, hlam, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h15849, h15850, h15869, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h15847, hlam, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h15849, hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [hlam, p15871_0]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h15862, hlam, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                rcases p15871_3 (m.d 0 1) (by simp) with h15898 | h15898
                                · linarith only [h15898, hlam, p15871_0]
                                · rcases p15871_3 (m.d 1 2) (by simp) with h15900 | h15900
                                  · rcases p15871_3 (m.d 1 3) (by simp) with h15901 | h15901
                                    · linarith only [h15850, h15901, hlam]
                                    · linarith only [h10472, h15901, hlam]
                                  · linarith only [h0, h15900, hlam]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h15848, hlam, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h10472, hc01, hc15, hlam, hphi, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [h11379, h15850, h15869, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p15871_1]
                              · have p15871_0 := h15871c.1
                                have p15871_1 := h15871c.2.1
                                have p15871_2 := h15871c.2.2.1
                                have p15871_3 := h15871c.2.2.2
                                linarith only [hlam, p15871_0]
                      · linarith only [h12233, h15376, h15488, h15489, h15864, hc02, hc25, hlam, hphi]
                · linarith only [h12233, h15488, h15846, h15849, hlam]
              · linarith only [h0, h12233, h15846, h15848, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h12233, h15846, h15847, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15913 | h15913
            · linarith only [h0, h14944, h15846, h15913, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15915 | h15915
              · linarith only [h0, h15376, h15846, h15915, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15917 | h15917
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15918 | h15918
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15919 | h15919
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15920 | h15920
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15921 | h15921
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15922 | h15922
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15923 | h15923
                            · linarith only [h0, h14944, h15488, h15489, h15844, h15846, h15918, h15923, hc01, hc23, hlam, hphi, ht12]
                            · rcases h1bigk with h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c | h15925c
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h0, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h10472, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h11379, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h12013, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h15915, h15920, h15922, hc01, hc23, hlam, hphi, ht12, p15925_1]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h15846, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h15913, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h15915, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                rcases p15925_3 (m.d 0 1) (by simp) with h15936 | h15936
                                · linarith only [h15936, hlam, p15925_0]
                                · rcases p15925_3 (m.d 1 2) (by simp) with h15938 | h15938
                                  · linarith only [h15846, h15938, hlam]
                                  · linarith only [h0, h15938, hlam]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h0, h15846, hc01, hc23, hlam, hphi, ht12, p15925_1]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h15488, h15489, h15846, h15919, h15923, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15925_1]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h12013, h15846, hc01, hc23, hlam, hphi, ht12, p15925_1]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                rcases p15925_3 (m.d 0 1) (by simp) with h15945 | h15945
                                · linarith only [h15945, hlam, p15925_0]
                                · rcases p15925_3 (m.d 1 2) (by simp) with h15947 | h15947
                                  · linarith only [h15913, h15947, hlam]
                                  · linarith only [h0, h15947, hlam]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p15925_1]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h15917, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h15488, h15489, h15913, h15919, h15920, h15923, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p15925_1]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                rcases p15925_3 (m.d 0 1) (by simp) with h15954 | h15954
                                · linarith only [h15954, hlam, p15925_0]
                                · rcases p15925_3 (m.d 1 2) (by simp) with h15956 | h15956
                                  · linarith only [h15915, h15956, hlam]
                                  · linarith only [h0, h15956, hlam]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p15925_1]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h15918, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [h15919, hlam, p15925_0]
                              · have p15925_0 := h15925c.1
                                have p15925_1 := h15925c.2.1
                                have p15925_2 := h15925c.2.2.1
                                have p15925_3 := h15925c.2.2.2
                                linarith only [hlam, p15925_0]
                          · linarith only [h0, h15913, h15922, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h15846, h15921, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h15488, h15489, h15846, h15918, h15920, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15966 | h15966
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15967 | h15967
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15968 | h15968
                          · linarith only [h11379, h15919, h15968, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h15913, h15968, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h12233, h15918, h15967, hc01, hc13, hlam, hphi]
                      · linarith only [h15488, h15489, h15846, h15918, h15966, hc05, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15973 | h15973
                    · linarith only [h0, h14944, h15844, h15917, h15918, h15973, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15975 | h15975
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15976 | h15976
                        · linarith only [h10472, h15918, h15976, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h15846, h15976, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h15488, h15846, h15975, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h10472, h15488, h15917, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h15981 | h15981
      · rcases m.htr 0 4 5 (by decide) (by decide) with h15982 | h15982
        · rcases m.htr 1 2 3 (by decide) (by decide) with h15983 | h15983
          · rcases m.htr 1 2 4 (by decide) (by decide) with h15984 | h15984
            · rcases m.htr 1 2 5 (by decide) (by decide) with h15985 | h15985
              · rcases m.htr 1 3 4 (by decide) (by decide) with h15986 | h15986
                · linarith only [h15488, h15981, h15986, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h15988 | h15988
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h15989 | h15989
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h15990 | h15990
                      · linarith only [h10472, h15986, h15990, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h15992 | h15992
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h15993 | h15993
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h15994 | h15994
                            · rcases h1bigk with h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c | h15995c
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h0, hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h10472, hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h11379, hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h12013, hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                rcases p15995_3 (m.d 0 1) (by simp) with h16001 | h16001
                                · linarith only [h16001, hlam, p15995_0]
                                · rcases p15995_3 (m.d 1 2) (by simp) with h16003 | h16003
                                  · rcases p15995_3 (m.d 1 3) (by simp) with h16004 | h16004
                                    · linarith only [h15983, h16004, hlam]
                                    · linarith only [h10472, h16004, hlam]
                                  · linarith only [h16003, hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h12233, h15981, h15983, h15994, hc12, hlam, hphi, ht01, ht0b, ht5b, p15995_1, u5ehi4]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h11379, hc01, hc12, hlam, hphi, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h12013, hc01, hc12, hlam, hphi, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h15986, hc01, hc34, hlam, hphi, ht12, ht23, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h15983, hlam, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h15986, hlam, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h0, h15376, h15985, hc01, hc13, hlam, hphi, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                rcases p15995_3 (m.d 0 1) (by simp) with h16017 | h16017
                                · linarith only [h16017, hlam, p15995_0]
                                · rcases p15995_3 (m.d 1 2) (by simp) with h16019 | h16019
                                  · rcases p15995_3 (m.d 1 3) (by simp) with h16020 | h16020
                                    · linarith only [h15986, h16020, hlam]
                                    · linarith only [h10472, h16020, hlam]
                                  · linarith only [h0, h16019, hlam]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h15984, hlam, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h10472, h15986, hc01, hc34, hlam, hphi, ht12, ht23, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h0, h15376, h15985, h15986, hc01, hc34, hlam, hphi, ht12, ht23, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h15986, h15988, hc01, hc34, hlam, hphi, ht12, ht23, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h15985, hlam, p15995_1]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h15988, hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [h15989, hlam, p15995_0]
                              · have p15995_0 := h15995c.1
                                have p15995_1 := h15995c.2.1
                                have p15995_2 := h15995c.2.2.1
                                have p15995_3 := h15995c.2.2.2
                                linarith only [hlam, p15995_0]
                            · linarith only [h10472, h15986, h15994, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h14944, h15982, h15993, hlam]
                        · linarith only [h12233, h15981, h15992, hlam]
                    · linarith only [h11379, h14944, h15982, h15984, h15989, hc01, hc12, hlam, hphi]
                  · linarith only [h12233, h15981, h15983, h15988, hlam]
              · linarith only [h14944, h15982, h15984, h15985, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h12233, h15981, h15983, h15984, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h16040 | h16040
            · linarith only [h0, h14944, h15983, h16040, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h16042 | h16042
              · linarith only [h0, h15376, h15983, h16042, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h16044 | h16044
                · linarith only [h15488, h15981, h16044, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16046 | h16046
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16047 | h16047
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16048 | h16048
                      · linarith only [h0, h16042, h16044, h16046, h16048, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h15983, h16048, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h10472, h15981, h15982, h16044, h16047, hc04, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h10472, h15981, h16046, hlam]
        · linarith only [h15488, h15981, h15982, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h16054 | h16054
        · rcases m.htr 1 2 3 (by decide) (by decide) with h16055 | h16055
          · rcases m.htr 1 2 4 (by decide) (by decide) with h16056 | h16056
            · rcases m.htr 1 2 5 (by decide) (by decide) with h16057 | h16057
              · rcases m.htr 1 3 4 (by decide) (by decide) with h16058 | h16058
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16059 | h16059
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16060 | h16060
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16061 | h16061
                      · linarith only [h10472, h15488, h16055, h16061, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h12233, h16055, h16058, h16061, hc01, hc12, hlam, hphi]
                    · linarith only [h11379, h14944, h16054, h16060, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h12233, h15488, h16058, h16059, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16066 | h16066
                  · linarith only [h0, h12233, h15981, h16058, h16066, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16068 | h16068
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16069 | h16069
                      · linarith only [h10472, h16058, h16069, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16071 | h16071
                        · linarith only [h16055, h16066, h16071, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h16073 | h16073
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h16074 | h16074
                            · rcases h1bigk with h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c | h16075c
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h0, hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h10472, hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h11379, hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h12013, hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                rcases p16075_3 (m.d 0 1) (by simp) with h16081 | h16081
                                · linarith only [h16081, hlam, p16075_0]
                                · rcases p16075_3 (m.d 1 2) (by simp) with h16083 | h16083
                                  · rcases p16075_3 (m.d 1 3) (by simp) with h16084 | h16084
                                    · linarith only [h16055, h16084, hlam]
                                    · linarith only [h10472, h16084, hlam]
                                  · linarith only [h16083, hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h0, h12233, h16055, hc01, hc12, hlam, hphi, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h0, h12233, h16055, h16066, h16068, hc01, hc12, hlam, hphi, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h0, h12233, h16055, h16066, hc01, hc12, hlam, hphi, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h16066, h16074, hc01, hc34, hlam, hphi, ht12, ht23, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h16055, hlam, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h16058, hlam, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h16066, hlam, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                rcases p16075_3 (m.d 0 1) (by simp) with h16097 | h16097
                                · linarith only [h16097, hlam, p16075_0]
                                · rcases p16075_3 (m.d 1 2) (by simp) with h16099 | h16099
                                  · rcases p16075_3 (m.d 1 3) (by simp) with h16100 | h16100
                                    · linarith only [h16058, h16100, hlam]
                                    · linarith only [h10472, h16100, hlam]
                                  · linarith only [h0, h16099, hlam]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h16056, hlam, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h10472, hc01, hc14, hlam, hphi, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h0, h12233, h16055, h16058, h16066, hc01, hc34, hlam, hphi, ht12, ht23, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                rcases p16075_3 (m.d 0 1) (by simp) with h16108 | h16108
                                · linarith only [h16108, hlam, p16075_0]
                                · rcases p16075_3 (m.d 1 2) (by simp) with h16110 | h16110
                                  · rcases p16075_3 (m.d 1 3) (by simp) with h16111 | h16111
                                    · linarith only [h16066, h16111, hlam]
                                    · linarith only [h10472, h16111, hlam]
                                  · linarith only [h0, h16110, hlam]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h16057, hlam, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h0, h12233, h16055, hc01, hc15, hlam, hphi, p16075_1]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [h16068, hlam, p16075_0]
                              · have p16075_0 := h16075c.1
                                have p16075_1 := h16075c.2.1
                                have p16075_2 := h16075c.2.2.1
                                have p16075_3 := h16075c.2.2.2
                                linarith only [hlam, p16075_0]
                            · linarith only [h11379, h14944, h16054, h16058, h16074, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h14944, h16054, h16073, hlam]
                    · linarith only [h11379, h14944, h16054, h16056, h16068, hc01, hc12, hlam, hphi]
              · linarith only [h14944, h16054, h16056, h16057, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
            · linarith only [h0, h12233, h16055, h16056, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h16124 | h16124
            · linarith only [h0, h14944, h16055, h16124, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h16126 | h16126
              · linarith only [h0, h15376, h16055, h16126, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h16128 | h16128
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16129 | h16129
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16130 | h16130
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16131 | h16131
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16132 | h16132
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h16133 | h16133
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h16134 | h16134
                            · rcases h1bigk with h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c | h16135c
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h0, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h10472, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h11379, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h12013, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h16126, h16131, h16133, hc01, hc23, hlam, hphi, ht12, p16135_1]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h16055, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h16124, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h16126, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                rcases p16135_3 (m.d 0 1) (by simp) with h16146 | h16146
                                · linarith only [h16146, hlam, p16135_0]
                                · rcases p16135_3 (m.d 1 2) (by simp) with h16148 | h16148
                                  · linarith only [h16055, h16148, hlam]
                                  · linarith only [h0, h16148, hlam]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p16135_1]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h11379, h16054, h16055, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p16135_1, u5ehi4]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h0, h16055, h16126, hc01, hc23, hlam, hphi, ht12, p16135_1]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                rcases p16135_3 (m.d 0 1) (by simp) with h16155 | h16155
                                · linarith only [h16155, hlam, p16135_0]
                                · rcases p16135_3 (m.d 1 2) (by simp) with h16157 | h16157
                                  · linarith only [h16124, h16157, hlam]
                                  · linarith only [h0, h16157, hlam]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h0, hc01, hc14, hlam, hphi, p16135_1]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h16128, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h0, h12233, h15981, h16124, h16129, h16131, hc01, hc23, hlam, hphi, ht12, p16135_1]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                rcases p16135_3 (m.d 0 1) (by simp) with h16164 | h16164
                                · linarith only [h16164, hlam, p16135_0]
                                · rcases p16135_3 (m.d 1 2) (by simp) with h16166 | h16166
                                  · linarith only [h16126, h16166, hlam]
                                  · linarith only [h0, h16166, hlam]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h0, hc01, hc15, hlam, hphi, p16135_1]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h16129, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [h16130, hlam, p16135_0]
                              · have p16135_0 := h16135c.1
                                have p16135_1 := h16135c.2.1
                                have p16135_2 := h16135c.2.2.1
                                have p16135_3 := h16135c.2.2.2
                                linarith only [hlam, p16135_0]
                            · linarith only [h15488, h16054, h16134, hlam]
                          · linarith only [h11379, h15488, h16054, h16124, h16133, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h16055, h16132, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h12233, h15981, h16055, h16129, h16131, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h11379, h15488, h16054, h16128, h16130, hc01, hc13, hlam, hphi]
                  · linarith only [h15488, h16054, h16128, h16129, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16179 | h16179
                  · linarith only [h0, h12233, h15981, h16128, h16179, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16181 | h16181
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16182 | h16182
                      · linarith only [h10472, h16128, h16182, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h16055, h16182, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h11379, h16054, h16181, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h16186 | h16186
          · rcases m.htr 1 2 4 (by decide) (by decide) with h16187 | h16187
            · rcases m.htr 1 2 5 (by decide) (by decide) with h16188 | h16188
              · rcases m.htr 1 3 4 (by decide) (by decide) with h16189 | h16189
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16190 | h16190
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16191 | h16191
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16192 | h16192
                      · linarith only [h0, h12233, h15488, h16186, h16192, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h12233, h16186, h16189, h16192, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16195 | h16195
                      · linarith only [h0, h12233, h15488, h16186, h16195, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h12233, h16189, h16191, h16195, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                  · linarith only [h0, h12233, h15488, h16189, h16190, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16199 | h16199
                  · linarith only [h0, h12233, h15981, h16189, h16199, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16201 | h16201
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16202 | h16202
                      · linarith only [h10472, h16189, h16202, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16204 | h16204
                        · linarith only [h16186, h16199, h16204, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h16206 | h16206
                          · linarith only [h0, h12233, h15488, h16054, h16187, h16206, hc01, hc12, hlam, hphi]
                          · linarith only [h0, h14944, h16201, h16206, hc01, hc14, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16209 | h16209
                      · linarith only [h0, h12233, h15488, h16186, h16199, h16209, hc01, hc35, hlam, hphi, ht12, ht23]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16211 | h16211
                        · linarith only [h0, h12233, h15981, h16186, h16211, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h16213 | h16213
                          · linarith only [h16187, h16201, h16213, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h16215 | h16215
                            · linarith only [h10472, h16189, h16201, h16215, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h0, h12233, h16186, h16189, h16215, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h12233, h16186, h16188, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h12233, h16186, h16187, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h16220 | h16220
            · linarith only [h0, h14944, h16186, h16220, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h16222 | h16222
              · linarith only [h0, h15376, h16186, h16222, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h16224 | h16224
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16225 | h16225
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16226 | h16226
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16227 | h16227
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16228 | h16228
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h16229 | h16229
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h16230 | h16230
                            · linarith only [h0, h12233, h15488, h16054, h16224, h16230, hc01, hc13, hlam, hphi]
                            · linarith only [h0, h12233, h15488, h16226, h16230, hc01, hc14, hlam, hphi]
                          · linarith only [h16220, h16226, h16229, hlam]
                        · linarith only [h16186, h16225, h16228, hlam]
                      · linarith only [h0, h12233, h15981, h16186, h16225, h16227, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16236 | h16236
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h16237 | h16237
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h16238 | h16238
                          · linarith only [h11379, h16226, h16238, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h16220, h16238, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h0, h12233, h16225, h16237, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h12233, h15981, h16186, h16225, h16236, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h12233, h15488, h16224, h16225, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h16244 | h16244
                  · linarith only [h0, h12233, h15981, h16224, h16244, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h16246 | h16246
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16247 | h16247
                      · linarith only [h10472, h16224, h16247, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h16186, h16247, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h16250 | h16250
                      · linarith only [h0, h16186, h16224, h16250, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h0, h16186, h16250, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 8040000 in
set_option maxHeartbeats 8040000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s15_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h12233 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  rcases m.htr 0 2 4 (by decide) (by decide) with h14944 | h14944
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s15_x1_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 h12233 h14944
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s15_x1_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 h12233 h14944

set_option maxHeartbeats 8040000 in
set_option maxHeartbeats 8040000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s15 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  rcases m.htr 0 2 3 (by decide) (by decide) with h12233 | h12233
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s15_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 h12233
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s15_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 h12233

end R2N4
