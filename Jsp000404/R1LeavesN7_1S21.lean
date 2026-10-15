import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S19
import Jsp000404.R1LeavesN7_1S20

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10050000 in
set_option maxHeartbeats 10050000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h9029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h9030 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h7821 := hg7821
  rcases m.htr 0 3 5 (by decide) (by decide) with h9642 | h9642
  · rcases m.htr 0 4 5 (by decide) (by decide) with h9643 | h9643
    · rcases m.htr 1 2 3 (by decide) (by decide) with h9644 | h9644
      · linarith only [h0, h4, h9644, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h9646 | h9646
        · linarith only [h0, h7821, h9646, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h9648 | h9648
          · rcases m.htr 1 3 4 (by decide) (by decide) with h9649 | h9649
            · linarith only [h1, h9030, h9642, h9649, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h9651 | h9651
              · rcases m.htr 1 4 5 (by decide) (by decide) with h9652 | h9652
                · rcases m.htr 2 3 4 (by decide) (by decide) with h9653 | h9653
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9654 | h9654
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9655 | h9655
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9656 | h9656
                        · rcases h0bigk with h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c | h9657c
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            rcases p9657_3 (m.d 0 1) (by simp) with h9659 | h9659
                            · rcases p9657_3 (m.d 0 2) (by simp) with h9660 | h9660
                              · linarith only [h0, h9660, hlam]
                              · rcases p9657_3 (m.d 0 3) (by simp) with h9662 | h9662
                                · linarith only [h1, h9662, hlam]
                                · linarith only [h4, h9662, hlam]
                            · linarith only [h0, h9659, hlam]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            rcases p9657_3 (m.d 0 1) (by simp) with h9666 | h9666
                            · rcases p9657_3 (m.d 0 2) (by simp) with h9667 | h9667
                              · linarith only [h0, h9667, hlam]
                              · rcases p9657_3 (m.d 0 3) (by simp) with h9669 | h9669
                                · linarith only [h1, h9669, hlam]
                                · rcases p9657_3 (m.d 0 4) (by simp) with h9671 | h9671
                                  · linarith only [h2, h9671, hlam]
                                  · linarith only [h9030, h9671, hlam]
                            · linarith only [h1, h9666, hlam]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            rcases p9657_3 (m.d 0 1) (by simp) with h9675 | h9675
                            · rcases p9657_3 (m.d 0 2) (by simp) with h9676 | h9676
                              · linarith only [h0, h9676, hlam]
                              · rcases p9657_3 (m.d 0 3) (by simp) with h9678 | h9678
                                · linarith only [h1, h9678, hlam]
                                · rcases p9657_3 (m.d 0 4) (by simp) with h9680 | h9680
                                  · linarith only [h2, h9680, hlam]
                                  · rcases p9657_3 (m.d 0 5) (by simp) with h9682 | h9682
                                    · linarith only [h3, h9682, hlam]
                                    · rcases h2bigk with h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h4, h9648, h9654, h9656, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9684_1]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h4, hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h7821, hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h4, h9030, h9653, h9654, h9656, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9684_1]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h0, hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h9644, hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h9646, hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h0, h4, h9030, h9653, h9654, h9656, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9684_1]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        rcases p9684_3 (m.d 0 2) (by simp) with h9695 | h9695
                                        · linarith only [h9695, hlam, p9684_0]
                                        · rcases p9684_3 (m.d 1 2) (by simp) with h9697 | h9697
                                          · linarith only [h9644, h9697, hlam]
                                          · rcases p9684_3 (m.d 2 3) (by simp) with h9699 | h9699
                                            · rcases p9684_3 (m.d 2 4) (by simp) with h9700 | h9700
                                              · linarith only [h9653, h9700, hlam]
                                              · linarith only [h7821, h9700, hlam]
                                            · linarith only [h9699, hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        rcases p9684_3 (m.d 0 2) (by simp) with h9704 | h9704
                                        · linarith only [h4, h9704, hlam]
                                        · linarith only [h0, h9704, hlam]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h4, h9030, h9653, hc02, hc23, hlam, hphi, p9684_1]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h0, h4, h9030, h9648, h9653, hlam, p9684_2]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        rcases p9684_3 (m.d 0 2) (by simp) with h9710 | h9710
                                        · linarith only [h9710, hlam, p9684_0]
                                        · rcases p9684_3 (m.d 1 2) (by simp) with h9712 | h9712
                                          · linarith only [h9646, h9712, hlam]
                                          · rcases p9684_3 (m.d 2 3) (by simp) with h9714 | h9714
                                            · rcases p9684_3 (m.d 2 4) (by simp) with h9715 | h9715
                                              · rcases p9684_3 (m.d 2 5) (by simp) with h9716 | h9716
                                                · linarith only [h9655, h9716, hlam]
                                                · rcases h3bigk with h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c | h9718c
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9030, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p9657_1, p9718_1]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h4, hlam, p9718_1]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9030, hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9030, h9653, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p9718_1]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h1, hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9644, hlam, p9718_1]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9649, hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h1, h9030, h9653, h9656, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9718_1]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    rcases p9718_3 (m.d 0 3) (by simp) with h9729 | h9729
                                                    · linarith only [h4, h9729, hlam]
                                                    · rcases p9718_3 (m.d 1 3) (by simp) with h9731 | h9731
                                                      · linarith only [h9644, h9731, hlam]
                                                      · rcases p9718_3 (m.d 2 3) (by simp) with h9733 | h9733
                                                        · rcases p9718_3 (m.d 3 4) (by simp) with h9734 | h9734
                                                          · linarith only [h9653, h9734, hlam]
                                                          · linarith only [h9030, h9734, hlam]
                                                        · linarith only [h4, h9733, hlam]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    rcases p9718_3 (m.d 0 3) (by simp) with h9738 | h9738
                                                    · linarith only [h4, h9738, hlam]
                                                    · linarith only [h1, h9738, hlam]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h4, h9030, hc02, hc23, hlam, hphi, p9718_1]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9030, h9642, h9653, hlam, p9718_2]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h0, h4, h9648, h9653, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p9718_1]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9644, h9648, h9653, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p9718_1]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9653, hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    rcases p9718_3 (m.d 0 3) (by simp) with h9748 | h9748
                                                    · linarith only [h9030, h9748, hlam]
                                                    · linarith only [h9642, h9748, hlam]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9642, hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9651, hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9654, hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [h9656, hlam, p9718_0]
                                                  · have p9718_0 := h9718c.1
                                                    have p9718_1 := h9718c.2.1
                                                    have p9718_2 := h9718c.2.2.1
                                                    have p9718_3 := h9718c.2.2.2
                                                    linarith only [hlam, p9718_0]
                                              · linarith only [h9715, hlam, p9684_0]
                                            · linarith only [h4, h9714, hlam]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        rcases p9684_3 (m.d 0 2) (by simp) with h9758 | h9758
                                        · linarith only [h7821, h9758, hlam]
                                        · linarith only [h0, h9758, hlam]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h9653, hlam, p9684_1]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        rcases p9684_3 (m.d 0 2) (by simp) with h9763 | h9763
                                        · linarith only [h7821, h9763, hlam]
                                        · linarith only [h9029, h9763, hlam]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h9029, hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h9648, hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h9654, hlam, p9684_1]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [h9655, hlam, p9684_0]
                                      · have p9684_0 := h9684c.1
                                        have p9684_1 := h9684c.2.1
                                        have p9684_2 := h9684c.2.2.1
                                        have p9684_3 := h9684c.2.2.2
                                        linarith only [hlam, p9684_0]
                            · linarith only [h2, h9675, hlam]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            rcases p9657_3 (m.d 0 1) (by simp) with h9772 | h9772
                            · rcases p9657_3 (m.d 0 2) (by simp) with h9773 | h9773
                              · linarith only [h0, h9773, hlam]
                              · linarith only [h9029, h9773, hlam]
                            · linarith only [h3, h9772, hlam]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h0, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h4, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h7821, hlam, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h3, h4, h9030, h9648, h9653, h9654, h9656, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h1, hlam, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9030, h9653, hc02, hc23, hlam, hphi, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9030, hlam, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h3, h9030, h9648, h9653, h9654, h9656, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h2, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h0, h9030, h9648, h9653, h9654, h9656, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h0, h4, h9030, h9648, h9653, h9654, h9656, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            rcases p9657_3 (m.d 0 1) (by simp) with h9791 | h9791
                            · rcases p9657_3 (m.d 0 2) (by simp) with h9792 | h9792
                              · linarith only [h7821, h9792, hlam]
                              · linarith only [h9029, h9792, hlam]
                            · linarith only [h3, h9791, hlam]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h3, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9029, hlam, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9642, hlam, p9657_0]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [h9643, hlam, p9657_1]
                          · have p9657_0 := h9657c.1
                            have p9657_1 := h9657c.2.1
                            have p9657_2 := h9657c.2.2.1
                            have p9657_3 := h9657c.2.2.2
                            linarith only [hlam, p9657_0]
                        · linarith only [h0, h4, h9030, h9643, h9648, h9654, h9656, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h3, h7821, h9648, h9652, h9654, h9655, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h4, h9030, h9653, h9654, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h9804 | h9804
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h9805 | h9805
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h9806 | h9806
                        · rcases h0bigk with h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c | h9807c
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [hlam, p9807_0]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            rcases p9807_3 (m.d 0 1) (by simp) with h9809 | h9809
                            · rcases p9807_3 (m.d 0 2) (by simp) with h9810 | h9810
                              · linarith only [h0, h9810, hlam]
                              · rcases p9807_3 (m.d 0 3) (by simp) with h9812 | h9812
                                · linarith only [h1, h9812, hlam]
                                · linarith only [h4, h9812, hlam]
                            · linarith only [h0, h9809, hlam]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            rcases p9807_3 (m.d 0 1) (by simp) with h9816 | h9816
                            · rcases p9807_3 (m.d 0 2) (by simp) with h9817 | h9817
                              · linarith only [h0, h9817, hlam]
                              · rcases p9807_3 (m.d 0 3) (by simp) with h9819 | h9819
                                · linarith only [h1, h9819, hlam]
                                · rcases p9807_3 (m.d 0 4) (by simp) with h9821 | h9821
                                  · linarith only [h2, h9821, hlam]
                                  · linarith only [h9030, h9821, hlam]
                            · linarith only [h1, h9816, hlam]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            rcases p9807_3 (m.d 0 1) (by simp) with h9825 | h9825
                            · rcases p9807_3 (m.d 0 2) (by simp) with h9826 | h9826
                              · linarith only [h0, h9826, hlam]
                              · rcases p9807_3 (m.d 0 3) (by simp) with h9828 | h9828
                                · linarith only [h1, h9828, hlam]
                                · rcases p9807_3 (m.d 0 4) (by simp) with h9830 | h9830
                                  · linarith only [h2, h9830, hlam]
                                  · rcases p9807_3 (m.d 0 5) (by simp) with h9832 | h9832
                                    · linarith only [h3, h9832, hlam]
                                    · rcases h2bigk with h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c | h9834c
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h4, h9648, h9804, h9806, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p9834_1]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h4, hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h7821, hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h4, h9653, h9804, h9806, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9834_1]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h0, hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h9644, hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h9646, hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h0, h4, h9653, h9804, h9806, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9834_1]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h9653, hc02, hc34, hlam, hphi, ht23, p9834_1]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h9653, hc12, hc34, hlam, hphi, ht23, p9834_1]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h9653, hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        rcases p9834_3 (m.d 0 2) (by simp) with h9849 | h9849
                                        · linarith only [h4, h9849, hlam]
                                        · linarith only [h9029, h9849, hlam]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        rcases p9834_3 (m.d 0 2) (by simp) with h9852 | h9852
                                        · linarith only [h9852, hlam, p9834_0]
                                        · rcases p9834_3 (m.d 1 2) (by simp) with h9854 | h9854
                                          · linarith only [h9646, h9854, hlam]
                                          · rcases p9834_3 (m.d 2 3) (by simp) with h9856 | h9856
                                            · linarith only [h9653, h9856, hlam]
                                            · linarith only [h4, h9856, hlam]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        rcases p9834_3 (m.d 0 2) (by simp) with h9859 | h9859
                                        · linarith only [h7821, h9859, hlam]
                                        · linarith only [h0, h9859, hlam]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h0, h4, h9648, h9653, h9804, h9806, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9834_1]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        rcases p9834_3 (m.d 0 2) (by simp) with h9864 | h9864
                                        · linarith only [h7821, h9864, hlam]
                                        · linarith only [h9029, h9864, hlam]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h9029, hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h9648, hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h9804, hlam, p9834_1]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [h9805, hlam, p9834_0]
                                      · have p9834_0 := h9834c.1
                                        have p9834_1 := h9834c.2.1
                                        have p9834_2 := h9834c.2.2.1
                                        have p9834_3 := h9834c.2.2.2
                                        linarith only [hlam, p9834_0]
                            · linarith only [h2, h9825, hlam]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            rcases p9807_3 (m.d 0 1) (by simp) with h9873 | h9873
                            · rcases p9807_3 (m.d 0 2) (by simp) with h9874 | h9874
                              · linarith only [h0, h9874, hlam]
                              · linarith only [h9029, h9874, hlam]
                            · linarith only [h3, h9873, hlam]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h0, hlam, p9807_0]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [hlam, p9807_0]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h4, hlam, p9807_0]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h7821, hlam, p9807_1]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h3, h4, h9648, h9653, h9804, h9806, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9807_1]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h1, hlam, p9807_1]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h9030, hc02, hc34, hlam, hphi, ht23, p9807_1]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [hlam, p9807_0]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h9030, hlam, p9807_1]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            rcases p9807_3 (m.d 0 1) (by simp) with h9887 | h9887
                            · rcases p9807_3 (m.d 0 2) (by simp) with h9888 | h9888
                              · linarith only [h4, h9888, hlam]
                              · linarith only [h9029, h9888, hlam]
                            · linarith only [h3, h9887, hlam]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h2, hlam, p9807_0]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            rcases p9807_3 (m.d 0 1) (by simp) with h9893 | h9893
                            · rcases p9807_3 (m.d 0 2) (by simp) with h9894 | h9894
                              · linarith only [h7821, h9894, hlam]
                              · rcases p9807_3 (m.d 0 3) (by simp) with h9896 | h9896
                                · linarith only [h9030, h9896, hlam]
                                · linarith only [h4, h9896, hlam]
                            · linarith only [h0, h9893, hlam]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            rcases p9807_3 (m.d 0 1) (by simp) with h9900 | h9900
                            · rcases p9807_3 (m.d 0 2) (by simp) with h9901 | h9901
                              · linarith only [h7821, h9901, hlam]
                              · rcases p9807_3 (m.d 0 3) (by simp) with h9903 | h9903
                                · linarith only [h9030, h9903, hlam]
                                · rcases p9807_3 (m.d 0 4) (by simp) with h9905 | h9905
                                  · rcases p9807_3 (m.d 0 5) (by simp) with h9906 | h9906
                                    · linarith only [h9643, h9906, hlam]
                                    · rcases h2bigk with h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c | h9908c
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h4, h9648, h9653, h9804, h9806, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9908_1]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h4, hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h7821, hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h4, h7821, h9653, h9804, h9806, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9807_1, p9908_1]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h0, hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h9644, hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h9646, hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h0, h4, h7821, h9653, h9804, h9806, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9807_1, p9908_1]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h9653, hc02, hc34, hlam, hphi, ht23, p9908_1]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h9653, hc12, hc34, hlam, hphi, ht23, p9908_1]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h9653, hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        rcases p9908_3 (m.d 0 2) (by simp) with h9923 | h9923
                                        · linarith only [h4, h9923, hlam]
                                        · linarith only [h9029, h9923, hlam]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        rcases p9908_3 (m.d 0 2) (by simp) with h9926 | h9926
                                        · linarith only [h9926, hlam, p9908_0]
                                        · rcases p9908_3 (m.d 1 2) (by simp) with h9928 | h9928
                                          · linarith only [h9646, h9928, hlam]
                                          · rcases p9908_3 (m.d 2 3) (by simp) with h9930 | h9930
                                            · linarith only [h9653, h9930, hlam]
                                            · linarith only [h4, h9930, hlam]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        rcases p9908_3 (m.d 0 2) (by simp) with h9933 | h9933
                                        · linarith only [h7821, h9933, hlam]
                                        · linarith only [h0, h9933, hlam]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h0, h4, h9648, h9653, h9804, h9806, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p9908_1]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h0, h4, h7821, h9648, hlam, p9807_1, p9908_2]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h9029, hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h9648, hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h9804, hlam, p9908_1]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [h9805, hlam, p9908_0]
                                      · have p9908_0 := h9908c.1
                                        have p9908_1 := h9908c.2.1
                                        have p9908_2 := h9908c.2.2.1
                                        have p9908_3 := h9908c.2.2.2
                                        linarith only [hlam, p9908_0]
                                  · linarith only [h9030, h9905, hlam]
                            · linarith only [h1, h9900, hlam]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [hlam, p9807_0]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            rcases p9807_3 (m.d 0 1) (by simp) with h9947 | h9947
                            · rcases p9807_3 (m.d 0 2) (by simp) with h9948 | h9948
                              · linarith only [h7821, h9948, hlam]
                              · linarith only [h9029, h9948, hlam]
                            · linarith only [h3, h9947, hlam]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h3, hlam, p9807_0]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h9029, hlam, p9807_1]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h9642, hlam, p9807_0]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [h9643, hlam, p9807_1]
                          · have p9807_0 := h9807c.1
                            have p9807_1 := h9807c.2.1
                            have p9807_2 := h9807c.2.2.1
                            have p9807_3 := h9807c.2.2.2
                            linarith only [hlam, p9807_0]
                        · linarith only [h9030, h9643, h9806, hlam]
                      · linarith only [h0, h3, h7821, h9648, h9652, h9804, h9805, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h4, h9642, h9648, h9804, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h9644, h9648, h9649, h9652, hlam]
              · linarith only [h9030, h9642, h9644, h9648, h9651, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · linarith only [h4, h9029, h9648, hc12, hc23, hlam, hphi]
    · linarith only [h4, h9029, h9030, h9643, hlam]
  · linarith only [h4, h9029, h9642, hlam]

set_option maxHeartbeats 10050000 in
set_option maxHeartbeats 10050000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h9029 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h7821 := hg7821
  rcases m.htr 0 3 4 (by decide) (by decide) with h9030 | h9030
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 h9029 h9030
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 h9029 h9030

set_option maxHeartbeats 10050000 in
set_option maxHeartbeats 10050000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h7821 := hg7821
  exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s13 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4 h7821 h9029

set_option maxHeartbeats 10050000 in
set_option maxHeartbeats 10050000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h7821 := hg7821
  rcases m.htr 0 2 5 (by decide) (by decide) with h9029 | h9029
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 h9029
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s12_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 h9029

set_option maxHeartbeats 12466000 in
set_option maxHeartbeats 12466000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s11_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h7821 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h7822 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7823 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7824 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7825 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h7826 | h7826
  · linarith only [h0, h4, h7821, h7826, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h7828 | h7828
    · rcases m.htr 1 2 5 (by decide) (by decide) with h7829 | h7829
      · rcases m.htr 1 3 4 (by decide) (by decide) with h7830 | h7830
        · rcases m.htr 1 3 5 (by decide) (by decide) with h7831 | h7831
          · rcases m.htr 1 4 5 (by decide) (by decide) with h7832 | h7832
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7833 | h7833
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7834 | h7834
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7835 | h7835
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7836 | h7836
                    · rcases h0bigk with h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c | h7837c
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h0, h7828, h7833, h7836, hc01, hc45, hlam, hphi, ht0b, ht5b, p7837_1]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h0, h4, h7828, h7833, h7836, hc01, hc45, hlam, hphi, ht0b, ht5b, p7837_1]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        rcases p7837_3 (m.d 0 1) (by simp) with h7841 | h7841
                        · rcases p7837_3 (m.d 0 2) (by simp) with h7842 | h7842
                          · linarith only [h0, h7842, hlam]
                          · linarith only [h7821, h7842, hlam]
                        · linarith only [h2, h7841, hlam]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        rcases p7837_3 (m.d 0 1) (by simp) with h7846 | h7846
                        · rcases p7837_3 (m.d 0 2) (by simp) with h7847 | h7847
                          · linarith only [h0, h7847, hlam]
                          · linarith only [h7822, h7847, hlam]
                        · linarith only [h3, h7846, hlam]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h0, hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h4, hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h4, h7821, h7833, h7836, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7837_1]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        rcases p7837_3 (m.d 0 1) (by simp) with h7855 | h7855
                        · rcases p7837_3 (m.d 0 2) (by simp) with h7856 | h7856
                          · rcases p7837_3 (m.d 0 3) (by simp) with h7857 | h7857
                            · rcases p7837_3 (m.d 0 4) (by simp) with h7858 | h7858
                              · linarith only [h7821, h7858, hlam]
                              · linarith only [h7825, h7858, hlam]
                            · linarith only [h7824, h7857, hlam]
                          · linarith only [h7822, h7856, hlam]
                        · linarith only [h3, h7855, hlam]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h1, hlam, p7837_1]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h0, h1, h7828, h7833, h7836, hc01, hc45, hlam, hphi, ht0b, ht5b, p7837_1]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        rcases p7837_3 (m.d 0 1) (by simp) with h7867 | h7867
                        · rcases p7837_3 (m.d 0 2) (by simp) with h7868 | h7868
                          · linarith only [h4, h7868, hlam]
                          · linarith only [h7821, h7868, hlam]
                        · linarith only [h2, h7867, hlam]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        rcases p7837_3 (m.d 0 1) (by simp) with h7872 | h7872
                        · rcases p7837_3 (m.d 0 2) (by simp) with h7873 | h7873
                          · linarith only [h4, h7873, hlam]
                          · linarith only [h7822, h7873, hlam]
                        · linarith only [h3, h7872, hlam]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h2, hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h7821, hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h7823, hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        rcases p7837_3 (m.d 0 1) (by simp) with h7881 | h7881
                        · rcases p7837_3 (m.d 0 2) (by simp) with h7882 | h7882
                          · rcases p7837_3 (m.d 0 3) (by simp) with h7883 | h7883
                            · rcases p7837_3 (m.d 0 4) (by simp) with h7884 | h7884
                              · rcases p7837_3 (m.d 0 5) (by simp) with h7885 | h7885
                                · linarith only [h7825, h7885, hlam]
                                · rcases h2bigk with h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c | h7887c
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7828, h7833, h7836, hc02, hc45, hlam, hphi, ht0b, ht5b, p7887_1]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h4, hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h4, h7833, h7836, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7887_1]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    rcases p7887_3 (m.d 0 2) (by simp) with h7892 | h7892
                                    · rcases p7887_3 (m.d 1 2) (by simp) with h7893 | h7893
                                      · linarith only [h0, h7893, hlam]
                                      · linarith only [h7829, h7893, hlam]
                                    · linarith only [h7892, hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h0, hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7826, hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h0, h7833, h7836, hc01, hc45, hlam, hphi, ht0b, ht5b, p7887_1]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    rcases p7887_3 (m.d 0 2) (by simp) with h7901 | h7901
                                    · rcases p7887_3 (m.d 1 2) (by simp) with h7902 | h7902
                                      · rcases p7887_3 (m.d 2 3) (by simp) with h7903 | h7903
                                        · rcases p7887_3 (m.d 2 4) (by simp) with h7904 | h7904
                                          · linarith only [h7828, h7904, hlam]
                                          · linarith only [h7835, h7904, hlam]
                                        · linarith only [h7834, h7903, hlam]
                                      · linarith only [h7902, hlam, p7887_0]
                                    · linarith only [h7822, h7901, hlam]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7821, h7833, h7836, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7887_1]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7828, h7833, h7836, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p7887_1]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    rcases p7887_3 (m.d 0 2) (by simp) with h7913 | h7913
                                    · linarith only [h4, h7913, hlam]
                                    · linarith only [h7821, h7913, hlam]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h3, h4, h7821, h7829, hlam, p7837_1, p7887_2]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7821, hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7828, hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7833, hlam, p7887_1]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h0, h7828, h7834, h7836, hc01, hc45, hlam, hphi, ht0b, ht5b, p7887_1]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7822, hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7829, hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7834, hlam, p7887_1]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [h7835, hlam, p7887_0]
                                  · have p7887_0 := h7887c.1
                                    have p7887_1 := h7887c.2.1
                                    have p7887_2 := h7887c.2.2.1
                                    have p7887_3 := h7887c.2.2.2
                                    linarith only [hlam, p7887_0]
                              · linarith only [h7825, h7884, hlam]
                            · linarith only [h7824, h7883, hlam]
                          · linarith only [h7822, h7882, hlam]
                        · linarith only [h3, h7881, hlam]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h3, hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h7822, hlam, p7837_1]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h7824, hlam, p7837_0]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [h7825, hlam, p7837_1]
                      · have p7837_0 := h7837c.1
                        have p7837_1 := h7837c.2.1
                        have p7837_2 := h7837c.2.2.1
                        have p7837_3 := h7837c.2.2.2
                        linarith only [hlam, p7837_0]
                    · linarith only [h0, h4, h7828, h7835, h7836, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7937 | h7937
                    · linarith only [h7833, h7835, h7937, hlam]
                    · rcases h0bigk with h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c | h7939c
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h2, h7821, h7832, h7833, h7835, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h2, h4, h7821, h7832, h7833, h7835, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h2, h7832, h7833, h7835, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        rcases p7939_3 (m.d 0 1) (by simp) with h7944 | h7944
                        · rcases p7939_3 (m.d 0 2) (by simp) with h7945 | h7945
                          · linarith only [h0, h7945, hlam]
                          · linarith only [h7822, h7945, hlam]
                        · linarith only [h3, h7944, hlam]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h0, hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h4, hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h2, h7832, h7833, h7835, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h3, h4, h7832, h7833, h7835, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h1, hlam, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h2, h4, h7821, h7832, h7833, h7835, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h2, h4, h7832, h7833, h7835, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        rcases p7939_3 (m.d 0 1) (by simp) with h7958 | h7958
                        · rcases p7939_3 (m.d 0 2) (by simp) with h7959 | h7959
                          · linarith only [h4, h7959, hlam]
                          · linarith only [h7822, h7959, hlam]
                        · linarith only [h3, h7958, hlam]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h2, hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h7821, hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h7823, hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h3, h4, h7821, h7832, h7833, h7835, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h3, hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h7822, hlam, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h7824, hlam, p7939_0]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [h7825, hlam, p7939_1]
                      · have p7939_0 := h7939c.1
                        have p7939_1 := h7939c.2.1
                        have p7939_2 := h7939c.2.2.1
                        have p7939_3 := h7939c.2.2.2
                        linarith only [hlam, p7939_0]
                · linarith only [h4, h7824, h7834, hlam]
              · linarith only [h4, h7823, h7833, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h7975 | h7975
              · rcases m.htr 2 3 5 (by decide) (by decide) with h7976 | h7976
                · rcases m.htr 2 4 5 (by decide) (by decide) with h7977 | h7977
                  · linarith only [h7828, h7832, h7977, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h7979 | h7979
                    · linarith only [h7828, h7832, h7975, h7979, hlam]
                    · rcases h0bigk with h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c | h7981c
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h7821, h7825, h7828, h7832, h7975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h4, h7821, h7825, h7828, h7832, h7975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h7825, h7828, h7832, h7975, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        rcases p7981_3 (m.d 0 1) (by simp) with h7986 | h7986
                        · rcases p7981_3 (m.d 0 2) (by simp) with h7987 | h7987
                          · linarith only [h0, h7987, hlam]
                          · linarith only [h7822, h7987, hlam]
                        · linarith only [h3, h7986, hlam]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h0, hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h4, hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h7825, h7828, h7832, h7975, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h4, h7825, h7828, h7832, h7975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h1, hlam, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h4, h7821, h7825, h7828, h7832, h7975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h4, h7825, h7828, h7832, h7975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        rcases p7981_3 (m.d 0 1) (by simp) with h8000 | h8000
                        · rcases p7981_3 (m.d 0 2) (by simp) with h8001 | h8001
                          · linarith only [h4, h8001, hlam]
                          · linarith only [h7822, h8001, hlam]
                        · linarith only [h3, h8000, hlam]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h2, hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h7821, hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h7823, hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h4, h7821, h7825, h7828, h7832, h7975, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h3, hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h7822, hlam, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h7824, hlam, p7981_0]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [h7825, hlam, p7981_1]
                      · have p7981_0 := h7981c.1
                        have p7981_1 := h7981c.2.1
                        have p7981_2 := h7981c.2.2.1
                        have p7981_3 := h7981c.2.2.2
                        linarith only [hlam, p7981_0]
                · linarith only [h4, h7824, h7976, hlam]
              · linarith only [h4, h7821, h7825, h7828, h7832, h7975, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h7826, h7829, h7831, hlam]
        · linarith only [h7826, h7828, h7830, hlam]
      · linarith only [h4, h7822, h7829, hc12, hc23, hlam, hphi]
    · linarith only [h4, h7821, h7828, hc12, hc23, hlam, hphi]

end R2N4
