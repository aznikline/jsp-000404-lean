import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S17
import Jsp000404.R1LeavesN7_8S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7972000 in
set_option maxHeartbeats 7972000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12890 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h12963 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  rcases m.htr 1 2 3 (by decide) (by decide) with h13516 | h13516
  · rcases m.htr 1 2 4 (by decide) (by decide) with h13517 | h13517
    · rcases m.htr 1 2 5 (by decide) (by decide) with h13518 | h13518
      · rcases m.htr 1 3 4 (by decide) (by decide) with h13519 | h13519
        · rcases m.htr 1 3 5 (by decide) (by decide) with h13520 | h13520
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13521 | h13521
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13522 | h13522
              · linarith only [h13522, h9886, h9889, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13524 | h13524
                · linarith only [h12963, h13519, h13521, h13524, h9886, h9889, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13526 | h13526
                  · linarith only [h12963, h13526, h9887, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13528 | h13528
                    · linarith only [h12963, h13516, h13519, h13528, h7600, h9889, hc01, hc12, hlam, hphi]
                    · linarith only [h13516, h13519, h13521, h13528, h7600, h9889, hc01, hc12, hlam, hphi]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13531 | h13531
              · linarith only [h13531, h9886, h9889, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13533 | h13533
                · linarith only [h12890, h13533, h9886, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13535 | h13535
                  · linarith only [h13519, h13521, h13535, h7600, h9889, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13537 | h13537
                    · linarith only [h13519, h13521, h13537, hlam]
                    · rcases h0bigk with h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c | h13539c
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [hlam, p13539_0]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h0, hlam, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h7600, hlam, p13539_0]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h8836, hlam, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h9666, hlam, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        rcases p13539_3 (m.d 0 1) (by simp) with h13545 | h13545
                        · linarith only [h0, h13545, hlam]
                        · rcases p13539_3 (m.d 0 2) (by simp) with h13547 | h13547
                          · rcases p13539_3 (m.d 0 3) (by simp) with h13548 | h13548
                            · linarith only [h13548, h9886, hlam]
                            · linarith only [h13548, h7600, hlam]
                          · linarith only [h0, h13547, hlam]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [hlam, p13539_0]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        rcases p13539_3 (m.d 0 1) (by simp) with h13553 | h13553
                        · linarith only [h0, h13553, hlam]
                        · rcases p13539_3 (m.d 0 2) (by simp) with h13555 | h13555
                          · rcases p13539_3 (m.d 0 3) (by simp) with h13556 | h13556
                            · linarith only [h13556, h9886, hlam]
                            · rcases p13539_3 (m.d 0 4) (by simp) with h13558 | h13558
                              · linarith only [h13558, h9887, hlam]
                              · linarith only [h13558, h9889, hlam]
                          · linarith only [h13555, h9886, hlam]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        rcases p13539_3 (m.d 0 1) (by simp) with h13562 | h13562
                        · linarith only [h0, h13562, hlam]
                        · rcases p13539_3 (m.d 0 2) (by simp) with h13564 | h13564
                          · rcases p13539_3 (m.d 0 3) (by simp) with h13565 | h13565
                            · linarith only [h13565, h9886, hlam]
                            · rcases p13539_3 (m.d 0 4) (by simp) with h13567 | h13567
                              · linarith only [h13567, h9887, hlam]
                              · rcases p13539_3 (m.d 0 5) (by simp) with h13569 | h13569
                                · linarith only [h13569, h9888, hlam]
                                · linarith only [h12963, h13569, hlam]
                          · linarith only [h13564, h9887, hlam]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        rcases p13539_3 (m.d 0 1) (by simp) with h13573 | h13573
                        · linarith only [h0, h13573, hlam]
                        · rcases p13539_3 (m.d 0 2) (by simp) with h13575 | h13575
                          · rcases p13539_3 (m.d 0 3) (by simp) with h13576 | h13576
                            · linarith only [h13576, h9886, hlam]
                            · rcases p13539_3 (m.d 0 4) (by simp) with h13578 | h13578
                              · linarith only [h13578, h9887, hlam]
                              · rcases p13539_3 (m.d 0 5) (by simp) with h13580 | h13580
                                · linarith only [h13580, h9888, hlam]
                                · rcases h2bigk with h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c | h13582c
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h0, hlam, p13582_1]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    rcases p13582_3 (m.d 0 2) (by simp) with h13585 | h13585
                                    · rcases p13582_3 (m.d 1 2) (by simp) with h13586 | h13586
                                      · rcases p13582_3 (m.d 2 3) (by simp) with h13587 | h13587
                                        · linarith only [h13587, hlam, p13582_0]
                                        · rcases p13582_3 (m.d 2 4) (by simp) with h13589 | h13589
                                          · linarith only [h13589, h9887, hlam]
                                          · linarith only [h13531, h13589, hlam]
                                      · linarith only [h13516, h13586, hlam]
                                    · linarith only [h13585, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    rcases p13582_3 (m.d 0 2) (by simp) with h13594 | h13594
                                    · rcases p13582_3 (m.d 1 2) (by simp) with h13595 | h13595
                                      · rcases p13582_3 (m.d 2 3) (by simp) with h13596 | h13596
                                        · linarith only [h13596, h9886, hlam]
                                        · rcases p13582_3 (m.d 2 4) (by simp) with h13598 | h13598
                                          · linarith only [h13598, hlam, p13582_0]
                                          · rcases p13582_3 (m.d 2 5) (by simp) with h13600 | h13600
                                            · linarith only [h13600, h9888, hlam]
                                            · linarith only [h13535, h13600, hlam]
                                      · linarith only [h13517, h13595, hlam]
                                    · linarith only [h13594, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    rcases p13582_3 (m.d 0 2) (by simp) with h13605 | h13605
                                    · rcases p13582_3 (m.d 1 2) (by simp) with h13606 | h13606
                                      · rcases p13582_3 (m.d 2 3) (by simp) with h13607 | h13607
                                        · linarith only [h13607, h9886, hlam]
                                        · rcases p13582_3 (m.d 2 4) (by simp) with h13609 | h13609
                                          · linarith only [h13609, h9887, hlam]
                                          · rcases p13582_3 (m.d 2 5) (by simp) with h13611 | h13611
                                            · linarith only [h13611, hlam, p13582_0]
                                            · rcases h3bigk with h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c | h13613c
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h7600, hlam, p13613_1]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h9889, hc23, hc34, hlam, hphi, p13613_1]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h9889, hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h12890, hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                rcases p13613_3 (m.d 0 3) (by simp) with h13619 | h13619
                                                · linarith only [h13619, h7600, hlam]
                                                · rcases p13613_3 (m.d 1 3) (by simp) with h13621 | h13621
                                                  · rcases p13613_3 (m.d 2 3) (by simp) with h13622 | h13622
                                                    · linarith only [h13516, h13622, hlam]
                                                    · rcases p13613_3 (m.d 3 4) (by simp) with h13624 | h13624
                                                      · linarith only [h13519, h13624, hlam]
                                                      · linarith only [h13624, h9889, hlam]
                                                  · linarith only [h13621, h7600, hlam]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                rcases p13613_3 (m.d 0 3) (by simp) with h13629 | h13629
                                                · linarith only [h13629, h7600, hlam]
                                                · linarith only [h13629, h9886, hlam]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13516, h7600, h9889, hc01, hc12, hlam, hphi, p13613_1]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h12890, h13516, h7600, hc01, hc12, hlam, hphi, p13613_1]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h9886, hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13516, hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13531, hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13533, hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13516, h13519, h7600, hc01, hc12, hlam, hphi, p13613_1]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13519, hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13519, h13521, hc23, hc45, hlam, hphi, ht34, p13613_1]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13537, hlam, p13613_1]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13516, h13520, h7600, hc01, hc12, hlam, hphi, p13613_1]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13520, hlam, p13613_0]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                rcases p13613_3 (m.d 0 3) (by simp) with h13646 | h13646
                                                · linarith only [h12890, h13646, hlam]
                                                · linarith only [h13646, h9886, hlam]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [h13516, h13520, h7600, h9889, hc01, hc12, hlam, hphi, p13613_1]
                                              · have p13613_0 := h13613c.1
                                                have p13613_1 := h13613c.2.1
                                                have p13613_2 := h13613c.2.2.1
                                                have p13613_3 := h13613c.2.2.2
                                                linarith only [hlam, p13613_0]
                                      · linarith only [h13518, h13606, hlam]
                                    · linarith only [h13605, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h12963, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p13539_1, p13582_1]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    rcases p13582_3 (m.d 0 2) (by simp) with h13655 | h13655
                                    · linarith only [h0, h13655, hlam]
                                    · linarith only [h13655, h9886, hlam]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    rcases p13582_3 (m.d 0 2) (by simp) with h13658 | h13658
                                    · linarith only [h0, h13658, hlam]
                                    · linarith only [h13658, h9887, hlam]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    rcases p13582_3 (m.d 0 2) (by simp) with h13661 | h13661
                                    · linarith only [h0, h13661, hlam]
                                    · linarith only [h13661, h9888, hlam]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h9886, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h13516, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h13531, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h13533, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h9887, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h13517, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h13521, h8836, h9887, hc23, hc45, hlam, hphi, ht34, p13582_1]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h13535, hlam, p13582_1]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h9888, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h13518, hlam, p13582_0]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h0, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13539_1, p13582_1]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [h0, h9888, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p13539_1, p13582_1]
                                  · have p13582_0 := h13582c.1
                                    have p13582_1 := h13582c.2.1
                                    have p13582_2 := h13582c.2.2.1
                                    have p13582_3 := h13582c.2.2.2
                                    linarith only [hlam, p13582_0]
                          · linarith only [h13575, h9888, hlam]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h9889, hc01, hc34, hlam, hphi, ht12, ht23, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h9886, hlam, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [hlam, p13539_0]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h9889, hlam, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h12890, hlam, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h13521, h8836, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h9887, hlam, p13539_0]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h13521, h8836, hc03, hc45, hlam, hphi, ht34, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [hlam, p13539_0]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h12963, hlam, p13539_0]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h12890, h13516, h13520, hc01, hc12, hlam, hphi, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h9888, hlam, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h12890, h13516, h13520, h7600, hc01, hc12, hlam, hphi, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [h12890, h13516, h13520, h8836, hc01, hc12, hlam, hphi, p13539_1]
                      · have p13539_0 := h13539c.1
                        have p13539_1 := h13539c.2.1
                        have p13539_2 := h13539c.2.2.1
                        have p13539_3 := h13539c.2.2.2
                        linarith only [hlam, p13539_0]
          · linarith only [h13519, h13520, h7600, h9889, hc01, hc35, hlam, hphi, ht12, ht23]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h13696 | h13696
          · linarith only [h12890, h13519, h13696, h7600, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13698 | h13698
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13699 | h13699
              · linarith only [h13519, h13699, h7600, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13701 | h13701
                · linarith only [h12963, h13696, h13701, h9666, h9886, h9889, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13703 | h13703
                  · linarith only [h0, h12963, h13703, h7600, h9887, h9889, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13705 | h13705
                    · rcases h0bigk with h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c | h13706c
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [hlam, p13706_0]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h0, hlam, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h7600, hlam, p13706_0]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h8836, hlam, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h9666, hlam, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        rcases p13706_3 (m.d 0 1) (by simp) with h13712 | h13712
                        · linarith only [h0, h13712, hlam]
                        · rcases p13706_3 (m.d 0 2) (by simp) with h13714 | h13714
                          · rcases p13706_3 (m.d 0 3) (by simp) with h13715 | h13715
                            · linarith only [h13715, h9886, hlam]
                            · linarith only [h13715, h7600, hlam]
                          · linarith only [h0, h13714, hlam]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [hlam, p13706_0]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        rcases p13706_3 (m.d 0 1) (by simp) with h13720 | h13720
                        · linarith only [h0, h13720, hlam]
                        · rcases p13706_3 (m.d 0 2) (by simp) with h13722 | h13722
                          · rcases p13706_3 (m.d 0 3) (by simp) with h13723 | h13723
                            · linarith only [h13723, h9886, hlam]
                            · rcases p13706_3 (m.d 0 4) (by simp) with h13725 | h13725
                              · linarith only [h13725, h9887, hlam]
                              · linarith only [h13725, h9889, hlam]
                          · linarith only [h13722, h9886, hlam]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        rcases p13706_3 (m.d 0 1) (by simp) with h13729 | h13729
                        · linarith only [h0, h13729, hlam]
                        · rcases p13706_3 (m.d 0 2) (by simp) with h13731 | h13731
                          · rcases p13706_3 (m.d 0 3) (by simp) with h13732 | h13732
                            · linarith only [h13732, h9886, hlam]
                            · rcases p13706_3 (m.d 0 4) (by simp) with h13734 | h13734
                              · linarith only [h13734, h9887, hlam]
                              · rcases p13706_3 (m.d 0 5) (by simp) with h13736 | h13736
                                · linarith only [h13736, h9888, hlam]
                                · linarith only [h12963, h13736, hlam]
                          · linarith only [h13731, h9887, hlam]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        rcases p13706_3 (m.d 0 1) (by simp) with h13740 | h13740
                        · linarith only [h0, h13740, hlam]
                        · rcases p13706_3 (m.d 0 2) (by simp) with h13742 | h13742
                          · rcases p13706_3 (m.d 0 3) (by simp) with h13743 | h13743
                            · linarith only [h13743, h9886, hlam]
                            · rcases p13706_3 (m.d 0 4) (by simp) with h13745 | h13745
                              · linarith only [h13745, h9887, hlam]
                              · rcases p13706_3 (m.d 0 5) (by simp) with h13747 | h13747
                                · linarith only [h13747, h9888, hlam]
                                · rcases h2bigk with h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c | h13749c
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h0, hlam, p13749_1]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    rcases p13749_3 (m.d 0 2) (by simp) with h13752 | h13752
                                    · rcases p13749_3 (m.d 1 2) (by simp) with h13753 | h13753
                                      · rcases p13749_3 (m.d 2 3) (by simp) with h13754 | h13754
                                        · linarith only [h13754, hlam, p13749_0]
                                        · rcases p13749_3 (m.d 2 4) (by simp) with h13756 | h13756
                                          · linarith only [h13756, h9887, hlam]
                                          · linarith only [h13699, h13756, hlam]
                                      · linarith only [h13516, h13753, hlam]
                                    · linarith only [h13752, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    rcases p13749_3 (m.d 0 2) (by simp) with h13761 | h13761
                                    · rcases p13749_3 (m.d 1 2) (by simp) with h13762 | h13762
                                      · rcases p13749_3 (m.d 2 3) (by simp) with h13763 | h13763
                                        · linarith only [h13763, h9886, hlam]
                                        · rcases p13749_3 (m.d 2 4) (by simp) with h13765 | h13765
                                          · linarith only [h13765, hlam, p13749_0]
                                          · rcases p13749_3 (m.d 2 5) (by simp) with h13767 | h13767
                                            · linarith only [h13767, h9888, hlam]
                                            · linarith only [h13703, h13767, hlam]
                                      · linarith only [h13517, h13762, hlam]
                                    · linarith only [h13761, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    rcases p13749_3 (m.d 0 2) (by simp) with h13772 | h13772
                                    · rcases p13749_3 (m.d 1 2) (by simp) with h13773 | h13773
                                      · rcases p13749_3 (m.d 2 3) (by simp) with h13774 | h13774
                                        · linarith only [h13774, h9886, hlam]
                                        · rcases p13749_3 (m.d 2 4) (by simp) with h13776 | h13776
                                          · linarith only [h13776, h9887, hlam]
                                          · rcases p13749_3 (m.d 2 5) (by simp) with h13778 | h13778
                                            · linarith only [h13778, hlam, p13749_0]
                                            · rcases h3bigk with h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c | h13780c
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h7600, hlam, p13780_1]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h12963, h13698, h9889, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13780_1]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h9889, hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h12890, hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h13696, h7600, hc01, hc35, hlam, hphi, ht12, ht23, p13780_1]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h13696, hc23, hc35, hlam, hphi, p13780_1]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h13519, hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h13696, hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h9886, hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h13516, hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h13699, hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h13701, hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                rcases p13780_3 (m.d 0 3) (by simp) with h13796 | h13796
                                                · linarith only [h13796, hlam, p13780_0]
                                                · rcases p13780_3 (m.d 1 3) (by simp) with h13798 | h13798
                                                  · linarith only [h13519, h13798, hlam]
                                                  · linarith only [h13798, h7600, hlam]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h7600, hc01, hc34, hlam, hphi, ht12, ht23, p13780_1]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                rcases p13780_3 (m.d 0 3) (by simp) with h13802 | h13802
                                                · linarith only [h13802, h9889, hlam]
                                                · linarith only [h13802, h9886, hlam]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h12890, h7600, hc01, hc34, hlam, hphi, ht12, ht23, p13780_1]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                rcases p13780_3 (m.d 0 3) (by simp) with h13807 | h13807
                                                · linarith only [h13807, hlam, p13780_0]
                                                · rcases p13780_3 (m.d 1 3) (by simp) with h13809 | h13809
                                                  · linarith only [h13696, h13809, hlam]
                                                  · linarith only [h13809, h7600, hlam]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h7600, hc01, hc35, hlam, hphi, ht12, ht23, p13780_1]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                rcases p13780_3 (m.d 0 3) (by simp) with h13813 | h13813
                                                · linarith only [h12890, h13813, hlam]
                                                · linarith only [h13813, h9886, hlam]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [h13705, hlam, p13780_0]
                                              · have p13780_0 := h13780c.1
                                                have p13780_1 := h13780c.2.1
                                                have p13780_2 := h13780c.2.2.1
                                                have p13780_3 := h13780c.2.2.2
                                                linarith only [hlam, p13780_0]
                                      · linarith only [h13518, h13773, hlam]
                                    · linarith only [h13772, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p13706_1, p13749_1, u5ehi0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    rcases p13749_3 (m.d 0 2) (by simp) with h13822 | h13822
                                    · linarith only [h0, h13822, hlam]
                                    · linarith only [h13822, h9886, hlam]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    rcases p13749_3 (m.d 0 2) (by simp) with h13825 | h13825
                                    · linarith only [h0, h13825, hlam]
                                    · linarith only [h13825, h9887, hlam]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    rcases p13749_3 (m.d 0 2) (by simp) with h13828 | h13828
                                    · linarith only [h0, h13828, hlam]
                                    · linarith only [h13828, h9888, hlam]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h9886, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h13516, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h13699, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h13701, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h9887, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h13517, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h12963, h9887, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13706_1, p13749_1]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h13703, hlam, p13749_1]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h9888, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h13518, hlam, p13749_0]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h0, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13706_1, p13749_1]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [h0, h9888, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p13706_1, p13749_1]
                                  · have p13749_0 := h13749c.1
                                    have p13749_1 := h13749c.2.1
                                    have p13749_2 := h13749c.2.2.1
                                    have p13749_3 := h13749c.2.2.2
                                    linarith only [hlam, p13749_0]
                          · linarith only [h13742, h9888, hlam]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h9889, hc01, hc34, hlam, hphi, ht12, ht23, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h9886, hlam, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [hlam, p13706_0]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h9889, hlam, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h12890, hlam, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h12963, h13519, h13698, hc01, hc34, hlam, hphi, ht12, ht23, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h9887, hlam, p13706_0]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h12963, h13519, h13698, hc03, hc34, hlam, hphi, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [hlam, p13706_0]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h12963, hlam, p13706_0]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h12963, h13519, h13698, hc01, hc34, hlam, hphi, ht12, ht23, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h9888, hlam, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h12963, h13519, h13698, h7600, hc01, hc34, hlam, hphi, ht12, ht23, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [h12963, h13519, h13698, h8836, hc01, hc34, hlam, hphi, ht12, ht23, p13706_1]
                      · have p13706_0 := h13706c.1
                        have p13706_1 := h13706c.2.1
                        have p13706_2 := h13706c.2.2.1
                        have p13706_3 := h13706c.2.2.2
                        linarith only [hlam, p13706_0]
                    · linarith only [h13519, h13698, h13705, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13863 | h13863
              · linarith only [h13863, h9886, h9889, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13865 | h13865
                · linarith only [h12890, h13865, h9886, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13867 | h13867
                  · linarith only [h13519, h13698, h13867, h7600, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13869 | h13869
                    · linarith only [h13519, h13698, h13869, h7600, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h13519, h13869, h7600, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
      · linarith only [h0, h13518, h9888, hlam]
    · linarith only [h0, h13517, h9887, hlam]
  · linarith only [h0, h13516, h9886, hlam]

set_option maxHeartbeats 7972000 in
set_option maxHeartbeats 7972000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h12890 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  rcases m.htr 0 4 5 (by decide) (by decide) with h12963 | h12963
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 h9889 h12890 h12963
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 h9889 h12890 h12963

set_option maxHeartbeats 7972000 in
set_option maxHeartbeats 7972000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9889 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  rcases m.htr 0 3 5 (by decide) (by decide) with h12890 | h12890
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 h9889 h12890
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 h9889 h12890

set_option maxHeartbeats 7972000 in
set_option maxHeartbeats 7972000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg9888 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  have h9888 := hg9888
  rcases m.htr 0 3 4 (by decide) (by decide) with h9889 | h9889
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x0 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 h9889
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16_x1 m hb0 hb2 hb3 hb5 hg0 hg7600 hg8836 hg9666 hg9886 hg9887 hg9888 h9889

set_option maxHeartbeats 8230000 in
set_option maxHeartbeats 8230000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s15 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg9887 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  have h9887 := hg9887
  rcases m.htr 0 2 5 (by decide) (by decide) with h9888 | h9888
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s16 m hb0 hb2 hb3 hb5 h0 h7600 h8836 h9666 h9886 h9887 h9888
  · rcases m.htr 0 3 4 (by decide) (by decide) with h13875 | h13875
    · rcases m.htr 0 3 5 (by decide) (by decide) with h13876 | h13876
      · linarith only [h13876, h9886, h9888, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h13878 | h13878
        · linarith only [h13875, h13878, h9886, h9888, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13880 | h13880
          · rcases m.htr 1 2 4 (by decide) (by decide) with h13881 | h13881
            · rcases m.htr 1 2 5 (by decide) (by decide) with h13882 | h13882
              · rcases m.htr 1 3 4 (by decide) (by decide) with h13883 | h13883
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13884 | h13884
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h13885 | h13885
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13886 | h13886
                      · linarith only [h13882, h13886, h9886, h9888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h13875, h13882, h13886, h9886, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13889 | h13889
                      · linarith only [h13882, h13889, h9886, h9888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h13875, h13882, h13889, h9886, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h13892 | h13892
                    · linarith only [h13878, h13883, h13884, h13892, h8836, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13894 | h13894
                      · linarith only [h13882, h13894, h9886, h9888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h13875, h13882, h13894, h9886, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h13875, h13882, h13883, h7600, h9886, h9888, hc01, hc12, hlam, hphi]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h13898 | h13898
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13899 | h13899
                  · linarith only [h13875, h13876, h13880, h13882, h13899, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h13901 | h13901
                    · linarith only [h13878, h13881, h13882, h13901, h8836, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13903 | h13903
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h13904 | h13904
                        · linarith only [h0, h13882, h13899, h13904, h9886, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13906 | h13906
                          · linarith only [h13901, h13906, h8836, hc01, hc24, hlam, hphi, ht12]
                          · linarith only [h0, h13882, h13903, h13906, h9886, hc34, hc45, hlam, hphi]
                      · linarith only [h13875, h13876, h13903, hc23, hc35, hlam, hphi]
                · linarith only [h13875, h13898, h7600, hlam]
            · linarith only [h0, h13881, h9887, hlam]
          · linarith only [h0, h13880, h9886, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h13913 | h13913
      · linarith only [h13875, h13913, h9887, h9888, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h13915 | h13915
        · linarith only [h13915, h9887, h9888, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h13917 | h13917
          · rcases m.htr 1 2 4 (by decide) (by decide) with h13918 | h13918
            · rcases m.htr 1 2 5 (by decide) (by decide) with h13919 | h13919
              · rcases m.htr 1 3 4 (by decide) (by decide) with h13920 | h13920
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13921 | h13921
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h13922 | h13922
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13923 | h13923
                      · linarith only [h0, h13875, h13923, h7600, h9886, hc01, hc12, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h13925 | h13925
                        · linarith only [h13913, h13919, h13923, h13925, h9887, h9888, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13927 | h13927
                          · linarith only [h13917, h13921, h13925, h13927, h9887, h9888, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13929 | h13929
                            · linarith only [h13923, h13927, h13929, h9887, h9888, hc23, hc34, hlam, hphi]
                            · linarith only [h13875, h13917, h13920, h13922, h13929, h7600, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13932 | h13932
                      · linarith only [h13875, h13932, h7600, h9886, h9888, hc01, hc25, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h13934 | h13934
                        · linarith only [h13919, h13932, h13934, h9887, h9888, hc15, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13936 | h13936
                          · linarith only [h13917, h13921, h13922, h13934, h13936, h9887, h9888, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13938 | h13938
                            · linarith only [h13920, h13922, h13938, hlam]
                            · rcases h0bigk with h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c | h13940c
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [hlam, p13940_0]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h0, hlam, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h7600, hlam, p13940_0]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h8836, hlam, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h9666, hlam, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13917, h13921, h13934, h9888, hc01, hc12, hlam, hphi, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [hlam, p13940_0]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13917, h13921, h13934, h7600, h9888, hc01, hc12, hlam, hphi, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13917, h13921, h13934, h9888, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h9888, hlam, p13940_0]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13875, h13920, hc01, hc14, hlam, hphi, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h9886, hlam, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [hlam, p13940_0]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13875, hlam, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13913, hlam, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13917, h13921, h13922, h13932, h13934, h8836, h9887, h9888, hc01, hc12, hc23, hc45, hlam, hphi, ht34, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h9887, hlam, p13940_0]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13917, h13921, h13934, h9887, h9888, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [hlam, p13940_0]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13915, hlam, p13940_0]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13917, h13921, h13934, h9888, hc01, hc12, hlam, hphi, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13917, h13921, h13932, h13934, h9887, h9888, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13917, h13921, h13934, h7600, h9888, hc01, hc12, hlam, hphi, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [h13917, h13921, h13934, h8836, h9888, hc01, hc12, hlam, hphi, p13940_1]
                              · have p13940_0 := h13940c.1
                                have p13940_1 := h13940c.2.1
                                have p13940_2 := h13940c.2.2.1
                                have p13940_3 := h13940c.2.2.2
                                linarith only [hlam, p13940_0]
                  · linarith only [h13875, h13920, h13921, h7600, hc01, hc35, hlam, hphi, ht12, ht23]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13967 | h13967
                  · linarith only [h13913, h13920, h13967, h7600, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h13969 | h13969
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13970 | h13970
                      · linarith only [h13920, h13970, h7600, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h13972 | h13972
                        · linarith only [h13919, h13970, h13972, h9887, h9888, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13974 | h13974
                          · linarith only [h13875, h13915, h13919, h13974, h7600, h9887, h9888, hc01, hc12, hlam, hphi]
                          · linarith only [h13920, h13969, h13970, h13974, h9887, h9888, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13977 | h13977
                      · linarith only [h13919, h13977, h9886, h9888, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h13979 | h13979
                        · linarith only [h13919, h13967, h13977, h13979, h9887, h9888, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13981 | h13981
                          · linarith only [h13919, h13969, h13981, h9887, h9888, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13983 | h13983
                            · linarith only [h13920, h13969, h13983, h7600, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h13920, h13983, h7600, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h13986 | h13986
                · linarith only [h13875, h13917, h13919, h13986, h7600, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h13988 | h13988
                  · linarith only [h13913, h13918, h13919, h13986, h13988, h7600, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h13990 | h13990
                    · linarith only [h13875, h13915, h13918, h13919, h13990, h7600, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h13992 | h13992
                      · linarith only [h0, h13919, h13986, h13992, h9886, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h13994 | h13994
                        · linarith only [h0, h13919, h13994, h9886, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h13996 | h13996
                          · linarith only [h13990, h13996, h8836, hc01, hc24, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h13998 | h13998
                            · linarith only [h0, h13919, h13996, h13998, hc01, hc34, hlam, hphi, ht12, ht23]
                            · linarith only [h13986, h13998, h7600, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
            · linarith only [h13917, h13918, h7600, h9887, h9888, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h0, h13917, h9886, hlam]

set_option maxHeartbeats 8762000 in
set_option maxHeartbeats 8762000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s14 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  have h9886 := hg9886
  rcases m.htr 0 2 4 (by decide) (by decide) with h9887 | h9887
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s15 m hb0 hb2 hb3 hb5 h0 h7600 h8836 h9666 h9886 h9887
  · rcases m.htr 0 2 5 (by decide) (by decide) with h14003 | h14003
    · rcases m.htr 0 3 4 (by decide) (by decide) with h14004 | h14004
      · linarith only [h14004, h9886, h9887, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h14006 | h14006
        · rcases m.htr 0 4 5 (by decide) (by decide) with h14007 | h14007
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14008 | h14008
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14009 | h14009
              · linarith only [h14003, h14009, h9887, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14011 | h14011
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14012 | h14012
                  · linarith only [h14004, h14006, h14012, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14014 | h14014
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14015 | h14015
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14016 | h14016
                        · linarith only [h14012, h14014, h14016, h9886, h9887, hc04, hlam, hphi, ht0b, ht5b, u5ehi1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14018 | h14018
                          · linarith only [h14016, h14018, h9886, h9887, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
                          · linarith only [h0, h14006, h14009, h14016, h14018, h9886, hc23, hc34, hlam, hphi]
                      · linarith only [h14003, h14007, h14015, h8836, h9887, hlam]
                    · linarith only [h14006, h14014, h7600, h8836, h9886, h9887, hc01, hc14, hlam, hphi]
                · linarith only [h0, h14003, h14011, hlam]
            · linarith only [h0, h14008, h9886, hlam]
          · linarith only [h14006, h14007, h9886, h9887, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h14026 | h14026
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14027 | h14027
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14028 | h14028
              · linarith only [h14003, h14028, h9887, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14030 | h14030
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14031 | h14031
                  · linarith only [h14004, h14027, h14028, h14031, h7600, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14033 | h14033
                    · linarith only [h14006, h14027, h14028, h14033, h7600, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14035 | h14035
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14036 | h14036
                        · linarith only [h14031, h14036, h7600, hc01, hc23, hlam, hphi, ht12]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14038 | h14038
                          · linarith only [h14033, h14038, h7600, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14040 | h14040
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14041 | h14041
                              · rcases h0bigk with h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c | h14042c
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [hlam, p14042_0]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h0, hlam, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h7600, hlam, p14042_0]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h8836, hlam, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h9666, hlam, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h0, h14028, h14036, hc01, hc34, hlam, hphi, ht12, ht23, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [hlam, p14042_0]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h0, h14028, h14036, hc03, hc34, hlam, hphi, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h9887, hlam, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h0, h14028, h14036, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p14042_1, u5ehi0]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h14033, h7600, hc01, hc35, hlam, hphi, ht12, ht23, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h9886, hlam, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [hlam, p14042_0]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h14004, hlam, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h14006, hlam, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  rcases p14042_3 (m.d 0 1) (by simp) with h14058 | h14058
                                  · linarith only [h14058, h8836, hlam]
                                  · rcases p14042_3 (m.d 0 2) (by simp) with h14060 | h14060
                                    · linarith only [h14060, h9887, hlam]
                                    · linarith only [h0, h14060, hlam]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h14003, h14028, h14036, h14038, h8836, hc23, hc34, hlam, hphi, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  rcases p14042_3 (m.d 0 1) (by simp) with h14064 | h14064
                                  · linarith only [h14064, h8836, hlam]
                                  · rcases p14042_3 (m.d 0 2) (by simp) with h14066 | h14066
                                    · linarith only [h14066, h9887, hlam]
                                    · linarith only [h14066, h9886, hlam]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [hlam, p14042_0]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  rcases p14042_3 (m.d 0 1) (by simp) with h14070 | h14070
                                  · linarith only [h14070, h8836, hlam]
                                  · rcases p14042_3 (m.d 0 2) (by simp) with h14072 | h14072
                                    · linarith only [h14072, h9887, hlam]
                                    · linarith only [h14003, h14072, hlam]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h14028, h14030, h14036, h9666, hc01, hc34, hlam, hphi, ht12, ht23, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h14003, hlam, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h0, h14003, h14028, h14036, hc03, hc34, hlam, hphi, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [h14026, hlam, p14042_1]
                                · have p14042_0 := h14042c.1
                                  have p14042_1 := h14042c.2.1
                                  have p14042_2 := h14042c.2.2.1
                                  have p14042_3 := h14042c.2.2.2
                                  linarith only [hlam, p14042_0]
                              · linarith only [h0, h14028, h14036, h14041, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                            · linarith only [h0, h14003, h14026, h14028, h14040, hlam]
                      · linarith only [h0, h14003, h14026, h14028, h14035, h8836, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h0, h14003, h14030, hlam]
            · linarith only [h0, h14027, h9886, hlam]
          · linarith only [h14003, h14026, h9887, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h14086 | h14086
      · linarith only [h14086, h9886, h9887, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h14088 | h14088
        · linarith only [h14003, h14088, h9886, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h14090 | h14090
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14091 | h14091
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14092 | h14092
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14093 | h14093
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14094 | h14094
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14095 | h14095
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14096 | h14096
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14097 | h14097
                        · linarith only [h14003, h14086, h14090, h14093, h14096, h14097, h9886, hc14, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14099 | h14099
                          · linarith only [h0, h14088, h14099, h7600, h9886, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14101 | h14101
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14102 | h14102
                              · rcases h0bigk with h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c | h14103c
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [hlam, p14103_0]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h0, hlam, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h7600, hlam, p14103_0]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h8836, hlam, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h9666, hlam, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14003, h14091, h14094, h14097, h14101, hc01, hc12, hlam, hphi, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [hlam, p14103_0]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14003, h14091, h14094, h14097, h14101, h7600, hc01, hc12, hlam, hphi, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h9887, hlam, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14003, hlam, p14103_0]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14003, h14091, h14094, h14097, h14101, h9886, hc01, hc12, hlam, hphi, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h9886, hlam, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [hlam, p14103_0]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14086, hlam, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14088, hlam, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14091, h14094, h14097, h9887, hc01, hc12, hlam, hphi, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14091, h14094, h14097, h9886, h9887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14091, h14094, h14097, h7600, h9887, hc01, hc12, hlam, hphi, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [hlam, p14103_0]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14091, h14094, h14097, h9887, hc12, hlam, hphi, ht01, ht0b, ht5b, p14103_1, u5ehi0]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14003, h14091, h14094, h14097, h14101, hc01, hc12, hlam, hphi, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14003, h14091, h14094, h14097, h14101, h9886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14003, h14091, h14094, h14097, h14101, h7600, hc01, hc12, hlam, hphi, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [h14090, hlam, p14103_1]
                                · have p14103_0 := h14103c.1
                                  have p14103_1 := h14103c.2.1
                                  have p14103_2 := h14103c.2.2.1
                                  have p14103_3 := h14103c.2.2.2
                                  linarith only [hlam, p14103_0]
                              · linarith only [h14097, h14102, h9886, h9887, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h14090, h14101, h9887, hlam]
                      · linarith only [h14090, h14096, h8836, h9887, hc01, hc24, hlam, hphi, ht12]
                    · linarith only [h14086, h14090, h14094, h14095, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14133 | h14133
                    · linarith only [h14088, h14094, h14133, h7600, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14135 | h14135
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14136 | h14136
                        · linarith only [h0, h14094, h14136, h7600, h9886, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14138 | h14138
                          · linarith only [h14003, h14093, h14133, h14138, h9886, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14140 | h14140
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14141 | h14141
                              · rcases h0bigk with h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c | h14142c
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [hlam, p14142_0]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h0, hlam, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h7600, hlam, p14142_0]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h8836, hlam, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h9666, hlam, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14003, h14092, h14140, hc01, hc12, hlam, hphi, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [hlam, p14142_0]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14003, h14092, h14140, h7600, hc01, hc12, hlam, hphi, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h9887, hlam, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14003, hlam, p14142_0]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14003, h14092, h14140, h9886, hc01, hc12, hlam, hphi, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h9886, hlam, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [hlam, p14142_0]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14086, hlam, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14088, hlam, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14092, h9887, hc01, hc12, hlam, hphi, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14092, h9886, h9887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14092, h7600, h9887, hc01, hc12, hlam, hphi, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [hlam, p14142_0]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14092, h9887, hc12, hlam, hphi, ht01, ht0b, ht5b, p14142_1, u5ehi0]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14003, h14092, h14140, hc01, hc12, hlam, hphi, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14003, h14092, h14140, h9886, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14003, h14092, h14140, h7600, hc01, hc12, hlam, hphi, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [h14090, hlam, p14142_1]
                                · have p14142_0 := h14142c.1
                                  have p14142_1 := h14142c.2.1
                                  have p14142_2 := h14142c.2.2.1
                                  have p14142_3 := h14142c.2.2.2
                                  linarith only [hlam, p14142_0]
                              · linarith only [h14092, h14094, h14141, h9886, h9887, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h14090, h14140, h9887, hlam]
                      · linarith only [h14090, h14092, h14135, h8836, h9887, hc01, hc12, hlam, hphi]
                · linarith only [h14092, h14093, h9886, h9887, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14172 | h14172
                · linarith only [h14003, h14092, h14172, h9886, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14174 | h14174
                  · linarith only [h14086, h14090, h14091, h14092, h14174, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14176 | h14176
                    · linarith only [h14003, h14088, h14174, h14176, h9886, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14178 | h14178
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14179 | h14179
                        · linarith only [h0, h14092, h14174, h14179, h9886, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14181 | h14181
                          · linarith only [h14176, h14181, h7600, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14183 | h14183
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h14184 | h14184
                              · rcases h0bigk with h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c | h14185c
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [hlam, p14185_0]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h0, hlam, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h7600, hlam, p14185_0]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h8836, hlam, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h9666, hlam, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h0, h14172, h14179, h14183, hc01, hc34, hlam, hphi, ht12, ht23, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [hlam, p14185_0]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h0, h14172, h14179, h14183, hc03, hc34, hlam, hphi, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h9887, hlam, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h14003, hlam, p14185_0]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h14091, h14172, h14179, h14183, h7600, hc01, hc34, hlam, hphi, ht12, ht23, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h9886, hlam, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [hlam, p14185_0]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h14086, hlam, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h14088, hlam, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  rcases p14185_3 (m.d 0 1) (by simp) with h14201 | h14201
                                  · linarith only [h14201, h8836, hlam]
                                  · rcases p14185_3 (m.d 0 2) (by simp) with h14203 | h14203
                                    · linarith only [h14203, h9887, hlam]
                                    · linarith only [h0, h14203, hlam]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h14179, h9886, h9887, hc23, hc34, hlam, hphi, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  rcases p14185_3 (m.d 0 1) (by simp) with h14207 | h14207
                                  · linarith only [h14207, h8836, hlam]
                                  · rcases p14185_3 (m.d 0 2) (by simp) with h14209 | h14209
                                    · linarith only [h14209, h9887, hlam]
                                    · linarith only [h14209, h9886, hlam]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [hlam, p14185_0]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h14003, h14092, h14179, h8836, h9886, hc23, hc34, hlam, hphi, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  rcases p14185_3 (m.d 0 1) (by simp) with h14214 | h14214
                                  · linarith only [h14214, h9666, hlam]
                                  · rcases p14185_3 (m.d 0 2) (by simp) with h14216 | h14216
                                    · linarith only [h14003, h14216, hlam]
                                    · linarith only [h0, h14216, hlam]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h14088, h14184, h9886, hc23, hc34, hlam, hphi, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  rcases p14185_3 (m.d 0 1) (by simp) with h14220 | h14220
                                  · linarith only [h14220, h9666, hlam]
                                  · rcases p14185_3 (m.d 0 2) (by simp) with h14222 | h14222
                                    · linarith only [h14003, h14222, hlam]
                                    · linarith only [h14222, h9886, hlam]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [h14090, hlam, p14185_1]
                                · have p14185_0 := h14185c.1
                                  have p14185_1 := h14185c.2.1
                                  have p14185_2 := h14185c.2.2.1
                                  have p14185_3 := h14185c.2.2.2
                                  linarith only [hlam, p14185_0]
                              · linarith only [h14179, h14184, h9886, h9887, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h14090, h14091, h14092, h14183, h7600, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h14090, h14178, h8836, hlam]
            · linarith only [h14091, h9886, h9887, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h14231 | h14231
            · rcases m.htr 1 2 4 (by decide) (by decide) with h14232 | h14232
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14233 | h14233
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14234 | h14234
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14235 | h14235
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14236 | h14236
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14237 | h14237
                        · linarith only [h14086, h14090, h14231, h14234, h14236, h14237, h7600, h9886, h9887, hc01, hc12, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14239 | h14239
                          · linarith only [h14088, h14090, h14231, h14234, h14236, h14239, h7600, h9886, h9887, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14241 | h14241
                            · linarith only [h14090, h14237, h14241, h9886, h9887, hc23, hc34, hlam, hphi]
                            · linarith only [h14231, h14234, h14236, h14241, h9886, h9887, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h14232, h14236, h9886, h9887, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h14086, h14234, h14235, h7600, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14246 | h14246
                    · linarith only [h14088, h14234, h14246, h7600, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14248 | h14248
                      · linarith only [h14090, h14234, h14248, h9886, h9887, hc23, hc34, hlam, hphi]
                      · linarith only [h14232, h14248, h9886, h9887, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h14232, h14233, h9886, h9887, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h14252 | h14252
                · linarith only [h14003, h14232, h14252, h9886, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h14254 | h14254
                  · linarith only [h14086, h14231, h14232, h14254, h7600, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h14256 | h14256
                    · linarith only [h14088, h14254, h14256, h7600, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h14258 | h14258
                      · linarith only [h14090, h14254, h14258, h9886, h9887, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h14260 | h14260
                        · linarith only [h14258, h14260, h8836, h9886, h9887, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h14262 | h14262
                          · linarith only [h14256, h14258, h14262, h7600, h8836, h9886, h9887, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h14264 | h14264
                            · linarith only [h14258, h14260, h14264, h8836, h9886, h9887, hc23, hc34, hlam, hphi]
                            · linarith only [h14264, h9886, h9887, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h14231, h9886, h9887, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 11598000 in
set_option maxHeartbeats 11598000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s13_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7600 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8836 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg9666 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h9886 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h7600 := hg7600
  have h8836 := hg8836
  have h9666 := hg9666
  exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s14 m hb0 hb2 hb3 hb5 h0 h7600 h8836 h9666 h9886

end R2N4
