import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S11
import Jsp000404.R1LeavesN7_10S22
import Jsp000404.R1LeavesN7_10S25

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h6875 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h8635 | h8635
  · rcases m.htr 0 2 5 (by decide) (by decide) with h8636 | h8636
    · rcases m.htr 0 3 4 (by decide) (by decide) with h8637 | h8637
      · rcases m.htr 0 4 5 (by decide) (by decide) with h8638 | h8638
        · rcases m.htr 1 2 3 (by decide) (by decide) with h8639 | h8639
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8640 | h8640
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8641 | h8641
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8642 | h8642
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8643 | h8643
                  · linarith only [h0, h6874, h6875, h8639, h8643, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h0, h6874, h6875, h8638, h8639, h8643, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h6875, h8636, h8637, h8639, h8642, hc03, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h6875, h8636, h8641, hc12, hc23, hlam, hphi]
            · linarith only [h6875, h8639, h8640, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8649 | h8649
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8650 | h8650
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8651 | h8651
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8652 | h8652
                  · linarith only [h0, h6874, h8639, h8652, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h6874, h8638, h8639, h8652, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · linarith only [h0, h6875, h8637, h8639, h8651, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h0, h6874, h8636, h8649, h8650, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h8635, h8649, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h8658 | h8658
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8659 | h8659
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8660 | h8660
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8661 | h8661
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8662 | h8662
                  · linarith only [h0, h6874, h6875, h8638, h8658, h8662, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8664 | h8664
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8665 | h8665
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8666 | h8666
                        · linarith only [h6874, h8638, h8659, h8666, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8668 | h8668
                          · linarith only [h6874, h8638, h8659, h8664, h8668, hlam]
                          · rcases h2bigk with h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c | h8670c
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h0, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h6875, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h6875, h8658, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8670_1]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h6875, h8658, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p8670_1]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              rcases p8670_3 (m.d 0 2) (by simp) with h8676 | h8676
                              · linarith only [h0, h8676, hlam]
                              · rcases p8670_3 (m.d 1 2) (by simp) with h8678 | h8678
                                · rcases p8670_3 (m.d 2 3) (by simp) with h8679 | h8679
                                  · linarith only [h8658, h8679, hlam]
                                  · linarith only [h6875, h8679, hlam]
                                · linarith only [h0, h8678, hlam]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h0, h6875, hc01, hc12, hlam, hphi, p8670_1]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h6875, h8636, h8658, h8666, hlam, p8670_2]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h6875, h8636, h8658, hlam, p8670_2]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h0, h6874, h8658, h8659, h8664, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8670_1]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h8658, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              rcases p8670_3 (m.d 0 2) (by simp) with h8690 | h8690
                              · linarith only [h6875, h8690, hlam]
                              · linarith only [h8635, h8690, hlam]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              rcases p8670_3 (m.d 0 2) (by simp) with h8693 | h8693
                              · linarith only [h6875, h8693, hlam]
                              · linarith only [h8636, h8693, hlam]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h8635, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h8659, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h8664, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h8666, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h8636, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h8660, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h8665, hlam, p8670_0]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [h6875, h8636, h8658, h8664, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8670_1]
                            · have p8670_0 := h8670c.1
                              have p8670_1 := h8670c.2.1
                              have p8670_2 := h8670c.2.2.1
                              have p8670_3 := h8670c.2.2.2
                              linarith only [hlam, p8670_0]
                      · linarith only [h6875, h8636, h8665, hlam]
                    · linarith only [h6875, h8637, h8664, hlam]
                · linarith only [h0, h6874, h6875, h8637, h8658, h8661, hlam]
              · linarith only [h6875, h8636, h8660, hc12, hc23, hlam, hphi]
            · linarith only [h6875, h8658, h8659, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8711 | h8711
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8712 | h8712
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8713 | h8713
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8714 | h8714
                  · linarith only [h0, h6874, h8658, h8714, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8716 | h8716
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8717 | h8717
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8718 | h8718
                        · linarith only [h0, h6874, h8658, h8711, h8714, h8718, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8720 | h8720
                          · linarith only [h6874, h8638, h8711, h8716, h8720, hlam]
                          · rcases h2bigk with h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c | h8722c
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h0, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h6875, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              rcases p8722_3 (m.d 0 2) (by simp) with h8726 | h8726
                              · rcases p8722_3 (m.d 1 2) (by simp) with h8727 | h8727
                                · rcases p8722_3 (m.d 2 3) (by simp) with h8728 | h8728
                                  · rcases p8722_3 (m.d 2 4) (by simp) with h8729 | h8729
                                    · linarith only [h8729, hlam, p8722_0]
                                    · rcases p8722_3 (m.d 2 5) (by simp) with h8731 | h8731
                                      · linarith only [h8636, h8731, hlam]
                                      · linarith only [h8718, h8731, hlam]
                                  · linarith only [h8716, h8728, hlam]
                                · linarith only [h8711, h8727, hlam]
                              · linarith only [h8726, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              rcases p8722_3 (m.d 0 2) (by simp) with h8737 | h8737
                              · rcases p8722_3 (m.d 1 2) (by simp) with h8738 | h8738
                                · rcases p8722_3 (m.d 2 3) (by simp) with h8739 | h8739
                                  · rcases p8722_3 (m.d 2 4) (by simp) with h8740 | h8740
                                    · linarith only [h8635, h8740, hlam]
                                    · rcases p8722_3 (m.d 2 5) (by simp) with h8742 | h8742
                                      · linarith only [h8742, hlam, p8722_0]
                                      · rcases h4bigk with h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c | h8744c
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8638, hc14, hc45, hlam, hphi, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h0, h6874, h8716, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h0, h6874, h8658, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8638, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h6874, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h0, h6874, h8658, h8716, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h0, h6874, h8658, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8714, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8635, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8711, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h0, h8635, h8658, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8718, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8637, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8713, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8716, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8720, hlam, p8744_0]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [hc04, hc45, hlam, hphi, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8711, hc24, hc45, hlam, hphi, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [h8716, hc34, hc45, hlam, hphi, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [hc34, hc45, hlam, hphi, p8744_1]
                                        · have p8744_0 := h8744c.1
                                          have p8744_1 := h8744c.2.1
                                          have p8744_2 := h8744c.2.2.1
                                          have p8744_3 := h8744c.2.2.2
                                          linarith only [hlam, p8744_0]
                                  · linarith only [h8717, h8739, hlam]
                                · linarith only [h8712, h8738, hlam]
                              · linarith only [h8737, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h8658, hc02, hc23, hlam, hphi, p8722_1]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h8658, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              rcases p8722_3 (m.d 0 2) (by simp) with h8776 | h8776
                              · linarith only [h0, h8776, hlam]
                              · linarith only [h8635, h8776, hlam]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              rcases p8722_3 (m.d 0 2) (by simp) with h8779 | h8779
                              · linarith only [h0, h8779, hlam]
                              · linarith only [h8636, h8779, hlam]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              rcases p8722_3 (m.d 0 2) (by simp) with h8782 | h8782
                              · linarith only [h8782, hlam, p8722_0]
                              · rcases p8722_3 (m.d 1 2) (by simp) with h8784 | h8784
                                · linarith only [h8658, h8784, hlam]
                                · linarith only [h0, h8784, hlam]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h0, h6874, h8711, h8716, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8722_1]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h0, h6874, h8658, h8711, hlam, p8722_2]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              rcases p8722_3 (m.d 0 2) (by simp) with h8790 | h8790
                              · linarith only [h6875, h8790, hlam]
                              · linarith only [h8636, h8790, hlam]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h8635, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h8711, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h8716, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h8718, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h8636, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h8712, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h8717, hlam, p8722_0]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [h0, h8636, h8658, h8716, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8722_1]
                            · have p8722_0 := h8722c.1
                              have p8722_1 := h8722c.2.1
                              have p8722_2 := h8722c.2.2.1
                              have p8722_3 := h8722c.2.2.2
                              linarith only [hlam, p8722_0]
                      · linarith only [h0, h6874, h8658, h8711, h8716, h8717, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h6874, h8658, h8711, h8716, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h6874, h8637, h8658, h8713, hlam]
              · linarith only [h0, h8636, h8712, hlam]
            · linarith only [h0, h8635, h8711, hlam]
      · linarith only [h0, h6874, h6875, h8637, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h8809 | h8809
      · rcases m.htr 0 4 5 (by decide) (by decide) with h8810 | h8810
        · linarith only [h0, h6874, h8636, h8810, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h8812 | h8812
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8813 | h8813
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8814 | h8814
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8815 | h8815
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8816 | h8816
                  · linarith only [h0, h6874, h8636, h8810, h8814, h8816, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8818 | h8818
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8819 | h8819
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8820 | h8820
                        · linarith only [h0, h6874, h8636, h8813, h8814, h8816, h8820, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8822 | h8822
                          · linarith only [h0, h6874, h8636, h8813, h8814, h8816, h8818, h8822, hlam]
                          · rcases h2bigk with h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c | h8824c
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h0, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h6875, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8636, h8812, h8819, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8824_1]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8636, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              rcases p8824_3 (m.d 0 2) (by simp) with h8830 | h8830
                              · linarith only [h0, h8830, hlam]
                              · rcases p8824_3 (m.d 1 2) (by simp) with h8832 | h8832
                                · rcases p8824_3 (m.d 2 3) (by simp) with h8833 | h8833
                                  · linarith only [h8812, h8833, hlam]
                                  · linarith only [h6875, h8833, hlam]
                                · linarith only [h0, h8832, hlam]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h0, h8636, h8819, hc01, hc12, hlam, hphi, p8824_1]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8635, h8636, h8812, h8819, hlam, p8824_2]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h0, h6874, h8636, h8813, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8824_1]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h0, h6874, h8812, h8813, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p8824_1]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8812, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              rcases p8824_3 (m.d 0 2) (by simp) with h8844 | h8844
                              · linarith only [h6875, h8844, hlam]
                              · linarith only [h8635, h8844, hlam]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h0, h6874, h8636, h8812, h8813, h8818, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p8824_1]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8635, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8813, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8818, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8820, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h0, h6874, h8813, h8814, h8816, h8818, hc34, hc45, hlam, hphi, p8824_1]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8814, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [h8819, hlam, p8824_0]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              rcases p8824_3 (m.d 0 2) (by simp) with h8856 | h8856
                              · linarith only [h8636, h8856, hlam]
                              · linarith only [h8635, h8856, hlam]
                            · have p8824_0 := h8824c.1
                              have p8824_1 := h8824c.2.1
                              have p8824_2 := h8824c.2.2.1
                              have p8824_3 := h8824c.2.2.2
                              linarith only [hlam, p8824_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8860 | h8860
                        · linarith only [h0, h6874, h6875, h8813, h8816, h8819, h8860, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h8862 | h8862
                          · linarith only [h0, h6874, h6875, h8813, h8816, h8818, h8819, h8862, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · linarith only [h0, h6874, h6875, h8819, h8862, hc14, hc45, hlam, hphi]
                    · linarith only [h0, h6874, h6875, h8809, h8813, h8818, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h6874, h6875, h8809, h8812, h8815, hlam]
              · linarith only [h0, h6875, h8812, h8814, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h6874, h6875, h8812, h8813, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h8869 | h8869
            · rcases m.htr 1 2 5 (by decide) (by decide) with h8870 | h8870
              · linarith only [h0, h6874, h8636, h8812, h8869, h8870, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h8872 | h8872
                · rcases m.htr 1 4 5 (by decide) (by decide) with h8873 | h8873
                  · linarith only [h0, h6874, h8812, h8873, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h8875 | h8875
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h8876 | h8876
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h8877 | h8877
                        · linarith only [h0, h6874, h8635, h8636, h8870, h8873, h8877, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h6874, h8869, h8870, h8875, h8877, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h6874, h8812, h8869, h8875, h8876, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h6874, h8812, h8869, h8875, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h6874, h8809, h8812, h8872, hlam]
            · linarith only [h0, h8635, h8869, hlam]
      · linarith only [h0, h6874, h6875, h8809, hlam]
  · linarith only [h0, h6874, h8635, hlam]

set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h6875 | h6875
  · exact r1l7_12_24_L_I_H_I_s6_x0_x0 m hb2 hb4 hg0 h6874 h6875
  · exact r1l7_12_24_L_I_H_I_s6_x0_x1 m hb2 hb4 hg0 h6874 h6875

set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6874 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  exact r1l7_12_24_L_I_H_I_s7 m hb2 hb4 h0 h6874

set_option maxHeartbeats 14456000 in
set_option maxHeartbeats 14456000 in
theorem r1l7_12_24_L_I_H_I_s6 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h6874 | h6874
  · exact r1l7_12_24_L_I_H_I_s6_x0 m hb2 hb4 hg0 h6874
  · exact r1l7_12_24_L_I_H_I_s6_x1 m hb2 hb4 hg0 h6874

set_option maxHeartbeats 28204000 in
set_option maxHeartbeats 28204000 in
theorem r1l7_12_24_L_I_H_I (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_12_24_L_I_H_I_s0 m hb2 hb4 h0
  · exact r1l7_12_24_L_I_H_I_s6 m hb2 hb4 h0

end R2N4
