import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S45

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18816 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18817 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18818 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h18819 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  rcases m.htr 0 3 5 (by decide) (by decide) with h19522 | h19522
  · rcases m.htr 0 4 5 (by decide) (by decide) with h19523 | h19523
    · rcases m.htr 1 2 3 (by decide) (by decide) with h19524 | h19524
      · rcases m.htr 1 2 4 (by decide) (by decide) with h19525 | h19525
        · rcases m.htr 1 2 5 (by decide) (by decide) with h19526 | h19526
          · rcases m.htr 1 3 4 (by decide) (by decide) with h19527 | h19527
            · rcases m.htr 1 3 5 (by decide) (by decide) with h19528 | h19528
              · rcases m.htr 1 4 5 (by decide) (by decide) with h19529 | h19529
                · rcases m.htr 2 3 4 (by decide) (by decide) with h19530 | h19530
                  · linarith only [h18816, h18819, h19530, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h19532 | h19532
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h19533 | h19533
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19534 | h19534
                        · rcases h0bigk with h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c | h19535c
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [hlam, p19535_0]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h0, hlam, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h14396, hlam, p19535_0]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h16915, hlam, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h14396, h18819, h19524, h19527, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            rcases p19535_3 (m.d 0 1) (by simp) with h19541 | h19541
                            · linarith only [h0, h19541, hlam]
                            · rcases p19535_3 (m.d 0 2) (by simp) with h19543 | h19543
                              · rcases p19535_3 (m.d 0 3) (by simp) with h19544 | h19544
                                · linarith only [h18816, h19544, hlam]
                                · linarith only [h14396, h19544, hlam]
                              · linarith only [h0, h19543, hlam]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [hlam, p19535_0]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            rcases p19535_3 (m.d 0 1) (by simp) with h19549 | h19549
                            · linarith only [h0, h19549, hlam]
                            · rcases p19535_3 (m.d 0 2) (by simp) with h19551 | h19551
                              · rcases p19535_3 (m.d 0 3) (by simp) with h19552 | h19552
                                · linarith only [h18816, h19552, hlam]
                                · rcases p19535_3 (m.d 0 4) (by simp) with h19554 | h19554
                                  · linarith only [h18817, h19554, hlam]
                                  · linarith only [h18819, h19554, hlam]
                              · linarith only [h18816, h19551, hlam]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            rcases p19535_3 (m.d 0 1) (by simp) with h19558 | h19558
                            · linarith only [h0, h19558, hlam]
                            · rcases p19535_3 (m.d 0 2) (by simp) with h19560 | h19560
                              · rcases p19535_3 (m.d 0 3) (by simp) with h19561 | h19561
                                · linarith only [h18816, h19561, hlam]
                                · rcases p19535_3 (m.d 0 4) (by simp) with h19563 | h19563
                                  · linarith only [h18817, h19563, hlam]
                                  · rcases p19535_3 (m.d 0 5) (by simp) with h19565 | h19565
                                    · linarith only [h18818, h19565, hlam]
                                    · rcases h2bigk with h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c | h19567c
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h0, hlam, p19567_1]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        rcases p19567_3 (m.d 0 2) (by simp) with h19570 | h19570
                                        · rcases p19567_3 (m.d 1 2) (by simp) with h19571 | h19571
                                          · rcases p19567_3 (m.d 2 3) (by simp) with h19572 | h19572
                                            · linarith only [h19572, hlam, p19567_0]
                                            · rcases p19567_3 (m.d 2 4) (by simp) with h19574 | h19574
                                              · linarith only [h18817, h19574, hlam]
                                              · linarith only [h19530, h19574, hlam]
                                          · linarith only [h19524, h19571, hlam]
                                        · linarith only [h19570, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        rcases p19567_3 (m.d 0 2) (by simp) with h19579 | h19579
                                        · rcases p19567_3 (m.d 1 2) (by simp) with h19580 | h19580
                                          · rcases p19567_3 (m.d 2 3) (by simp) with h19581 | h19581
                                            · linarith only [h18816, h19581, hlam]
                                            · rcases p19567_3 (m.d 2 4) (by simp) with h19583 | h19583
                                              · linarith only [h19583, hlam, p19567_0]
                                              · rcases p19567_3 (m.d 2 5) (by simp) with h19585 | h19585
                                                · linarith only [h18818, h19585, hlam]
                                                · rcases h3bigk with h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c | h19587c
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h14396, hlam, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h0, h18819, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19535_1, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h18819, hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h0, h18819, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p19535_1, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h14396, hc01, hc13, hlam, hphi, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19524, h19532, h19534, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h14396, h18815, h18819, h19524, h19528, h19534, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    rcases p19587_3 (m.d 0 3) (by simp) with h19597 | h19597
                                                    · linarith only [h14396, h19597, hlam]
                                                    · linarith only [h19522, h19597, hlam]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h18816, hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19524, hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19530, hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h18816, h19534, hc02, hc45, hlam, hphi, ht0b, ht5b, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h14396, h18815, h19526, h19527, h19532, h19534, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19527, hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19524, h19527, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19524, h19527, h19534, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19587_1]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19522, hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19528, hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19532, hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [h19534, hlam, p19587_0]
                                                  · have p19587_0 := h19587c.1
                                                    have p19587_1 := h19587c.2.1
                                                    have p19587_2 := h19587c.2.2.1
                                                    have p19587_3 := h19587c.2.2.2
                                                    linarith only [hlam, p19587_0]
                                          · linarith only [h19525, h19580, hlam]
                                        · linarith only [h19579, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h14396, h18815, h18819, h19526, hlam, p19535_1, p19567_2]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h18816, h19532, h19534, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19567_1]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        rcases p19567_3 (m.d 0 2) (by simp) with h19620 | h19620
                                        · linarith only [h0, h19620, hlam]
                                        · linarith only [h18816, h19620, hlam]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        rcases p19567_3 (m.d 0 2) (by simp) with h19623 | h19623
                                        · linarith only [h0, h19623, hlam]
                                        · linarith only [h18817, h19623, hlam]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h0, h14396, h18815, h18819, h19526, hlam, p19535_1, p19567_2]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h18816, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h19524, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h19530, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h18816, h18819, h19532, h19534, hc02, hc45, hlam, hphi, ht0b, ht5b, p19535_1, p19567_1]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h18817, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h19525, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h0, h18817, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19535_1, p19567_1]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h0, h18817, h19532, h19534, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19535_1, p19567_1]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h18818, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h19526, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h19532, hlam, p19567_1]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [h19533, hlam, p19567_0]
                                      · have p19567_0 := h19567c.1
                                        have p19567_1 := h19567c.2.1
                                        have p19567_2 := h19567c.2.2.1
                                        have p19567_3 := h19567c.2.2.2
                                        linarith only [hlam, p19567_0]
                              · linarith only [h18817, h19560, hlam]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            rcases p19535_3 (m.d 0 1) (by simp) with h19643 | h19643
                            · linarith only [h0, h19643, hlam]
                            · linarith only [h18815, h19643, hlam]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h18815, h18819, h19524, h19526, h19527, h19532, h19534, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h18816, hlam, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [hlam, p19535_0]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h18819, hlam, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h18819, h19524, h19527, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h18815, h18819, h19524, h19526, h19527, h19532, h19534, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h18817, hlam, p19535_0]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h14396, h18815, h18819, h19524, h19526, h19527, h19532, h19534, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [hlam, p19535_0]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            rcases p19535_3 (m.d 0 1) (by simp) with h19655 | h19655
                            · linarith only [h16915, h19655, hlam]
                            · linarith only [h18815, h19655, hlam]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h18815, hlam, p19535_0]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h18818, hlam, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h19522, hlam, p19535_0]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [h19523, hlam, p19535_1]
                          · have p19535_0 := h19535c.1
                            have p19535_1 := h19535c.2.1
                            have p19535_2 := h19535c.2.2.1
                            have p19535_3 := h19535c.2.2.2
                            linarith only [hlam, p19535_0]
                        · linarith only [h14396, h18815, h18819, h19523, h19526, h19532, h19534, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h14396, h18815, h18819, h19524, h19527, h19529, h19533, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h18819, h19522, h19524, h19527, h19532, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h16915, h19523, h19529, hlam]
              · linarith only [h14396, h19522, h19528, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h19668 | h19668
              · rcases m.htr 1 4 5 (by decide) (by decide) with h19669 | h19669
                · rcases m.htr 2 3 4 (by decide) (by decide) with h19670 | h19670
                  · linarith only [h0, h16915, h18815, h18816, h19526, h19527, h19670, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h19672 | h19672
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h19673 | h19673
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h19674 | h19674
                        · rcases h0bigk with h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c | h19675c
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [hlam, p19675_0]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h0, hlam, p19675_1]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h14396, hlam, p19675_0]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h16915, hlam, p19675_1]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h14396, h19527, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19675_1]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            rcases p19675_3 (m.d 0 1) (by simp) with h19681 | h19681
                            · linarith only [h0, h19681, hlam]
                            · rcases p19675_3 (m.d 0 2) (by simp) with h19683 | h19683
                              · rcases p19675_3 (m.d 0 3) (by simp) with h19684 | h19684
                                · linarith only [h18816, h19684, hlam]
                                · linarith only [h14396, h19684, hlam]
                              · linarith only [h0, h19683, hlam]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [hlam, p19675_0]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            rcases p19675_3 (m.d 0 1) (by simp) with h19689 | h19689
                            · linarith only [h0, h19689, hlam]
                            · rcases p19675_3 (m.d 0 2) (by simp) with h19691 | h19691
                              · rcases p19675_3 (m.d 0 3) (by simp) with h19692 | h19692
                                · linarith only [h18816, h19692, hlam]
                                · rcases p19675_3 (m.d 0 4) (by simp) with h19694 | h19694
                                  · linarith only [h18817, h19694, hlam]
                                  · linarith only [h18819, h19694, hlam]
                              · linarith only [h18816, h19691, hlam]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            rcases p19675_3 (m.d 0 1) (by simp) with h19698 | h19698
                            · linarith only [h0, h19698, hlam]
                            · rcases p19675_3 (m.d 0 2) (by simp) with h19700 | h19700
                              · rcases p19675_3 (m.d 0 3) (by simp) with h19701 | h19701
                                · linarith only [h18816, h19701, hlam]
                                · rcases p19675_3 (m.d 0 4) (by simp) with h19703 | h19703
                                  · linarith only [h18817, h19703, hlam]
                                  · rcases p19675_3 (m.d 0 5) (by simp) with h19705 | h19705
                                    · linarith only [h18818, h19705, hlam]
                                    · rcases h2bigk with h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c | h19707c
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h0, hlam, p19707_1]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        rcases p19707_3 (m.d 0 2) (by simp) with h19710 | h19710
                                        · rcases p19707_3 (m.d 1 2) (by simp) with h19711 | h19711
                                          · rcases p19707_3 (m.d 2 3) (by simp) with h19712 | h19712
                                            · linarith only [h19712, hlam, p19707_0]
                                            · rcases p19707_3 (m.d 2 4) (by simp) with h19714 | h19714
                                              · linarith only [h18817, h19714, hlam]
                                              · linarith only [h19670, h19714, hlam]
                                          · linarith only [h19524, h19711, hlam]
                                        · linarith only [h19710, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        rcases p19707_3 (m.d 0 2) (by simp) with h19719 | h19719
                                        · rcases p19707_3 (m.d 1 2) (by simp) with h19720 | h19720
                                          · rcases p19707_3 (m.d 2 3) (by simp) with h19721 | h19721
                                            · linarith only [h18816, h19721, hlam]
                                            · rcases p19707_3 (m.d 2 4) (by simp) with h19723 | h19723
                                              · linarith only [h19723, hlam, p19707_0]
                                              · rcases p19707_3 (m.d 2 5) (by simp) with h19725 | h19725
                                                · linarith only [h18818, h19725, hlam]
                                                · rcases h3bigk with h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c | h19727c
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h14396, hlam, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h0, h14396, h18815, h18819, h19526, h19527, h19672, h19674, hc12, hc23, hc34, hc45, hlam, hphi, ht01, ht0b, ht5b, p19675_1, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h18819, hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h0, h18819, h19674, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19675_1, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19527, hc03, hc34, hlam, hphi, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19527, hc23, hc34, hlam, hphi, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19527, hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19527, h19674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h18816, hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19524, hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19670, hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h0, h18816, h19674, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h14396, h18815, h19526, h19672, h19674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [hc13, hc34, hlam, hphi, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [hc23, hc34, hlam, hphi, p19727_1]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    rcases p19727_3 (m.d 0 3) (by simp) with h19747 | h19747
                                                    · linarith only [h18819, h19747, hlam]
                                                    · linarith only [h19522, h19747, hlam]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19522, hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19668, hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19672, hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [h19674, hlam, p19727_0]
                                                  · have p19727_0 := h19727c.1
                                                    have p19727_1 := h19727c.2.1
                                                    have p19727_2 := h19727c.2.2.1
                                                    have p19727_3 := h19727c.2.2.2
                                                    linarith only [hlam, p19727_0]
                                          · linarith only [h19525, h19720, hlam]
                                        · linarith only [h19719, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h16915, h18815, h19526, hlam, p19675_1, p19707_2]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p19675_1, p19707_1]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        rcases p19707_3 (m.d 0 2) (by simp) with h19760 | h19760
                                        · linarith only [h0, h19760, hlam]
                                        · linarith only [h18816, h19760, hlam]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        rcases p19707_3 (m.d 0 2) (by simp) with h19763 | h19763
                                        · linarith only [h0, h19763, hlam]
                                        · linarith only [h18817, h19763, hlam]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h0, h14396, h18815, h18819, h19526, hlam, p19675_1, p19707_2]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h18816, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h19524, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h19670, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h18816, h18819, h19672, h19674, hc02, hc45, hlam, hphi, ht0b, ht5b, p19675_1, p19707_1]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h18817, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h19525, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h0, h18817, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19675_1, p19707_1]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h0, h18817, h19672, h19674, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19675_1, p19707_1]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h18818, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h19526, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h19672, hlam, p19707_1]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [h19673, hlam, p19707_0]
                                      · have p19707_0 := h19707c.1
                                        have p19707_1 := h19707c.2.1
                                        have p19707_2 := h19707c.2.2.1
                                        have p19707_3 := h19707c.2.2.2
                                        linarith only [hlam, p19707_0]
                              · linarith only [h18817, h19700, hlam]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            rcases p19675_3 (m.d 0 1) (by simp) with h19783 | h19783
                            · linarith only [h0, h19783, hlam]
                            · linarith only [h18815, h19783, hlam]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h14396, h18815, h19526, h19527, h19672, h19674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19675_1]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h18816, hlam, p19675_1]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [hlam, p19675_0]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h18819, hlam, p19675_1]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            rcases p19675_3 (m.d 0 1) (by simp) with h19790 | h19790
                            · linarith only [h14396, h19790, hlam]
                            · linarith only [h18815, h19790, hlam]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            rcases p19675_3 (m.d 0 1) (by simp) with h19793 | h19793
                            · linarith only [h16915, h19793, hlam]
                            · rcases p19675_3 (m.d 0 2) (by simp) with h19795 | h19795
                              · rcases p19675_3 (m.d 0 3) (by simp) with h19796 | h19796
                                · linarith only [h18819, h19796, hlam]
                                · linarith only [h14396, h19796, hlam]
                              · linarith only [h0, h19795, hlam]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h18817, hlam, p19675_0]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            rcases p19675_3 (m.d 0 1) (by simp) with h19801 | h19801
                            · linarith only [h16915, h19801, hlam]
                            · rcases p19675_3 (m.d 0 2) (by simp) with h19803 | h19803
                              · rcases p19675_3 (m.d 0 3) (by simp) with h19804 | h19804
                                · linarith only [h18819, h19804, hlam]
                                · rcases p19675_3 (m.d 0 4) (by simp) with h19806 | h19806
                                  · rcases p19675_3 (m.d 0 5) (by simp) with h19807 | h19807
                                    · linarith only [h19523, h19807, hlam]
                                    · rcases h2bigk with h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c | h19809c
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h0, hlam, p19809_1]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        rcases p19809_3 (m.d 0 2) (by simp) with h19812 | h19812
                                        · rcases p19809_3 (m.d 1 2) (by simp) with h19813 | h19813
                                          · rcases p19809_3 (m.d 2 3) (by simp) with h19814 | h19814
                                            · linarith only [h19814, hlam, p19809_0]
                                            · rcases p19809_3 (m.d 2 4) (by simp) with h19816 | h19816
                                              · linarith only [h18817, h19816, hlam]
                                              · linarith only [h19670, h19816, hlam]
                                          · linarith only [h19524, h19813, hlam]
                                        · linarith only [h19812, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        rcases p19809_3 (m.d 0 2) (by simp) with h19821 | h19821
                                        · rcases p19809_3 (m.d 1 2) (by simp) with h19822 | h19822
                                          · rcases p19809_3 (m.d 2 3) (by simp) with h19823 | h19823
                                            · linarith only [h18816, h19823, hlam]
                                            · rcases p19809_3 (m.d 2 4) (by simp) with h19825 | h19825
                                              · linarith only [h19825, hlam, p19809_0]
                                              · rcases p19809_3 (m.d 2 5) (by simp) with h19827 | h19827
                                                · linarith only [h18818, h19827, hlam]
                                                · rcases h3bigk with h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c | h19829c
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h14396, hlam, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h16915, h19527, h19672, h19674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19675_1, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h18819, hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h16915, h19527, h19674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19675_1, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19527, hc03, hc34, hlam, hphi, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19527, h19672, h19674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19527, hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19527, h19674, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h18816, hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19524, hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19670, hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h0, h18816, h19674, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [hc03, hc34, hlam, hphi, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [hc13, hc34, hlam, hphi, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [hc23, hc34, hlam, hphi, p19829_1]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    rcases p19829_3 (m.d 0 3) (by simp) with h19849 | h19849
                                                    · linarith only [h18819, h19849, hlam]
                                                    · linarith only [h19522, h19849, hlam]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19522, hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19668, hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19672, hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [h19674, hlam, p19829_0]
                                                  · have p19829_0 := h19829c.1
                                                    have p19829_1 := h19829c.2.1
                                                    have p19829_2 := h19829c.2.2.1
                                                    have p19829_3 := h19829c.2.2.2
                                                    linarith only [hlam, p19829_0]
                                          · linarith only [h19525, h19822, hlam]
                                        · linarith only [h19821, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h14396, h18815, h18817, h19526, hlam, p19675_1, p19809_2]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h18816, h19672, h19674, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19809_1]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        rcases p19809_3 (m.d 0 2) (by simp) with h19862 | h19862
                                        · linarith only [h0, h19862, hlam]
                                        · linarith only [h18816, h19862, hlam]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        rcases p19809_3 (m.d 0 2) (by simp) with h19865 | h19865
                                        · linarith only [h0, h19865, hlam]
                                        · linarith only [h18817, h19865, hlam]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h0, h14396, h18815, h18817, h19526, hlam, p19675_1, p19809_2]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h18816, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h19524, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h19670, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h18816, h18817, h19672, h19674, hc02, hc45, hlam, hphi, ht0b, ht5b, p19675_1, p19809_1]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h18817, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h19525, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h0, h18817, h19672, h19674, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p19809_1]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        rcases p19809_3 (m.d 0 2) (by simp) with h19878 | h19878
                                        · rcases p19809_3 (m.d 1 2) (by simp) with h19879 | h19879
                                          · rcases p19809_3 (m.d 2 3) (by simp) with h19880 | h19880
                                            · linarith only [h19670, h19880, hlam]
                                            · linarith only [h19672, h19880, hlam]
                                          · linarith only [h19526, h19879, hlam]
                                        · linarith only [h18818, h19878, hlam]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h18818, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h19526, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h19672, hlam, p19809_1]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [h19673, hlam, p19809_0]
                                      · have p19809_0 := h19809c.1
                                        have p19809_1 := h19809c.2.1
                                        have p19809_2 := h19809c.2.2.1
                                        have p19809_3 := h19809c.2.2.2
                                        linarith only [hlam, p19809_0]
                                  · linarith only [h18819, h19806, hlam]
                              · linarith only [h18816, h19803, hlam]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [hlam, p19675_0]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            rcases p19675_3 (m.d 0 1) (by simp) with h19893 | h19893
                            · linarith only [h16915, h19893, hlam]
                            · linarith only [h18815, h19893, hlam]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h18815, hlam, p19675_0]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h18818, hlam, p19675_1]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h19522, hlam, p19675_0]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [h19523, hlam, p19675_1]
                          · have p19675_0 := h19675c.1
                            have p19675_1 := h19675c.2.1
                            have p19675_2 := h19675c.2.2.1
                            have p19675_3 := h19675c.2.2.2
                            linarith only [hlam, p19675_0]
                        · linarith only [h16915, h19523, h19527, h19674, hlam]
                      · linarith only [h14396, h18815, h19527, h19669, h19673, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h14396, h19522, h19527, h19672, hc23, hc34, hlam, hphi]
                · linarith only [h16915, h19523, h19669, hlam]
              · linarith only [h14396, h19522, h19668, hlam]
          · linarith only [h0, h18818, h19526, hlam]
        · linarith only [h0, h18817, h19525, hlam]
      · linarith only [h0, h18816, h19524, hlam]
    · linarith only [h14396, h18815, h18819, h19523, hlam]
  · linarith only [h14396, h18815, h19522, hlam]

set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18816 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18817 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18818 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  rcases m.htr 0 3 4 (by decide) (by decide) with h18819 | h18819
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815 h18816 h18817 h18818 h18819
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815 h18816 h18817 h18818 h18819

set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18816 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18817 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h18818 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  linarith only [h0, h18815, h18818, hlam]

set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18816 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18817 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h18818 | h18818
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815 h18816 h18817 h18818
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815 h18816 h18817 h18818

set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18816 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h18817 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h19912 | h19912
  · rcases m.htr 0 3 4 (by decide) (by decide) with h19913 | h19913
    · linarith only [h18816, h18817, h19913, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h19915 | h19915
      · rcases m.htr 0 4 5 (by decide) (by decide) with h19916 | h19916
        · rcases m.htr 1 2 3 (by decide) (by decide) with h19917 | h19917
          · rcases m.htr 1 2 4 (by decide) (by decide) with h19918 | h19918
            · rcases m.htr 1 2 5 (by decide) (by decide) with h19919 | h19919
              · rcases m.htr 1 3 4 (by decide) (by decide) with h19920 | h19920
                · rcases m.htr 1 3 5 (by decide) (by decide) with h19921 | h19921
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h19922 | h19922
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h19923 | h19923
                      · linarith only [h14396, h18815, h18816, h19913, h19919, h19923, hc02, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19925 | h19925
                        · linarith only [h18816, h18817, h19920, h19923, h19925, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h18815, h18817, h19917, h19920, h19921, h19923, h19925, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h16915, h19916, h19922, hlam]
                  · linarith only [h14396, h18815, h18816, h18817, h19915, h19921, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h19930 | h19930
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h19931 | h19931
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h19932 | h19932
                      · linarith only [h18816, h18817, h19918, h19932, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19934 | h19934
                        · linarith only [h18816, h18817, h19918, h19934, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h18816, h18817, h19915, h19918, h19934, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h18816, h18817, h19918, h19931, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h14396, h18815, h18816, h19915, h19919, h19930, hc02, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h18817, h19918, h19919, hc02, hc25, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h19940 | h19940
              · rcases m.htr 1 3 4 (by decide) (by decide) with h19941 | h19941
                · linarith only [h14396, h18815, h19913, h19917, h19918, h19940, h19941, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h19943 | h19943
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h19944 | h19944
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h19945 | h19945
                      · linarith only [h0, h16915, h18815, h18816, h19918, h19940, h19941, h19945, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h19947 | h19947
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h19948 | h19948
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h19949 | h19949
                            · rcases h0bigk with h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c | h19950c
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [hlam, p19950_0]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h0, hlam, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h14396, hlam, p19950_0]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h16915, hlam, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h0, h19918, h19945, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h0, h19918, h19945, hc01, hc34, hlam, hphi, ht12, ht23, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [hlam, p19950_0]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h0, h14396, h18815, h19918, h19940, h19945, h19947, h19949, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h18817, hlam, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                rcases p19950_3 (m.d 0 1) (by simp) with h19960 | h19960
                                · linarith only [h0, h19960, hlam]
                                · linarith only [h18815, h19960, hlam]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h14396, h18815, h19917, h19918, h19940, h19945, h19947, h19949, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h18816, hlam, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [hlam, p19950_0]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h19913, hlam, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                rcases p19950_3 (m.d 0 1) (by simp) with h19967 | h19967
                                · linarith only [h14396, h19967, hlam]
                                · linarith only [h18815, h19967, hlam]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                rcases p19950_3 (m.d 0 1) (by simp) with h19970 | h19970
                                · linarith only [h16915, h19970, hlam]
                                · rcases p19950_3 (m.d 0 2) (by simp) with h19972 | h19972
                                  · linarith only [h18817, h19972, hlam]
                                  · linarith only [h0, h19972, hlam]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h18816, h18817, h19945, hc23, hc34, hlam, hphi, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                rcases p19950_3 (m.d 0 1) (by simp) with h19976 | h19976
                                · linarith only [h16915, h19976, hlam]
                                · rcases p19950_3 (m.d 0 2) (by simp) with h19978 | h19978
                                  · linarith only [h18817, h19978, hlam]
                                  · linarith only [h18816, h19978, hlam]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [hlam, p19950_0]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                rcases p19950_3 (m.d 0 1) (by simp) with h19982 | h19982
                                · linarith only [h16915, h19982, hlam]
                                · linarith only [h18815, h19982, hlam]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h18815, hlam, p19950_0]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h19912, hlam, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h19915, hlam, p19950_0]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [h19916, hlam, p19950_1]
                              · have p19950_0 := h19950c.1
                                have p19950_1 := h19950c.2.1
                                have p19950_2 := h19950c.2.2.1
                                have p19950_3 := h19950c.2.2.2
                                linarith only [hlam, p19950_0]
                            · linarith only [h0, h19918, h19945, h19949, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · linarith only [h14396, h18815, h19917, h19918, h19944, h19948, hlam]
                        · linarith only [h14396, h19915, h19917, h19918, h19945, h19947, hc23, hc34, hlam, hphi]
                    · linarith only [h16915, h19916, h19944, hlam]
                  · linarith only [h14396, h18815, h19915, h19940, h19943, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h14396, h18815, h19912, h19917, h19940, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h18816, h19917, hlam]
        · linarith only [h16915, h18815, h19916, hlam]
      · linarith only [h14396, h18815, h19915, hlam]
  · linarith only [h0, h18815, h19912, hlam]

set_option maxHeartbeats 19848000 in
set_option maxHeartbeats 19848000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16915 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h18815 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h18816 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h18817 | h18817
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x0 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815 h18816 h18817
  · exact r1l7_10_12_23_L_I_L_I_H_I_s17_x0_x0_x1 m hb0 hb2 hb3 hg0 hg14396 hg16915 h18815 h18816 h18817

end R2N4
