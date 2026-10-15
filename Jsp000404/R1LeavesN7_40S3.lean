import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_40S2

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1488 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h1489 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h2661 | h2661
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2662 | h2662
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2663 | h2663
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2664 | h2664
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2665 | h2665
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2666 | h2666
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2667 | h2667
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2668 | h2668
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2669 | h2669
                  · linarith only [h1486, h1489, h2661, h2669, hc02, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2671 | h2671
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2672 | h2672
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2673 | h2673
                        · rcases h1bigk with h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c | h2674c
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h0, hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h927, hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h1488, h1489, h2661, h2666, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2674_1, u2ehi4]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h1241, hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            rcases p2674_3 (m.d 0 1) (by simp) with h2680 | h2680
                            · linarith only [h2680, hlam, p2674_0]
                            · rcases p2674_3 (m.d 1 2) (by simp) with h2682 | h2682
                              · rcases p2674_3 (m.d 1 3) (by simp) with h2683 | h2683
                                · linarith only [h2663, h2683, hlam]
                                · linarith only [h2683, h927, hlam]
                              · linarith only [h2682, hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h1488, h1489, h2661, h2666, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2674_1, u2ehi4]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h1241, h2668, hc01, hc12, hlam, hphi, p2674_1]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h1241, hc01, hc12, hlam, hphi, p2674_1]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            rcases p2674_3 (m.d 0 1) (by simp) with h2691 | h2691
                            · linarith only [h2691, hlam, p2674_0]
                            · rcases p2674_3 (m.d 1 2) (by simp) with h2693 | h2693
                              · rcases p2674_3 (m.d 1 3) (by simp) with h2694 | h2694
                                · rcases p2674_3 (m.d 1 4) (by simp) with h2695 | h2695
                                  · linarith only [h2666, h2695, hlam]
                                  · linarith only [h1488, h1489, h2661, h2666, h2695, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2674_1, u2ehi4]
                                · linarith only [h2694, hlam, p2674_0]
                              · linarith only [h0, h2693, hlam]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h2663, hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h1488, h1489, h2661, h2663, h2666, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2674_1, u2ehi4]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h1241, h2663, hc01, hc12, hlam, hphi, p2674_1]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            rcases p2674_3 (m.d 0 1) (by simp) with h2704 | h2704
                            · linarith only [h2704, hlam, p2674_0]
                            · rcases p2674_3 (m.d 1 2) (by simp) with h2706 | h2706
                              · rcases p2674_3 (m.d 1 3) (by simp) with h2707 | h2707
                                · rcases p2674_3 (m.d 1 4) (by simp) with h2708 | h2708
                                  · rcases p2674_3 (m.d 1 5) (by simp) with h2709 | h2709
                                    · linarith only [h2668, h2709, hlam]
                                    · linarith only [h1241, h2709, hlam]
                                  · linarith only [h2708, hlam, p2674_0]
                                · linarith only [h2707, h927, hlam]
                              · linarith only [h0, h2706, hlam]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h2664, hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h2666, hlam, p2674_1]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h1241, hc01, hc14, hlam, hphi, p2674_1]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            rcases p2674_3 (m.d 0 1) (by simp) with h2719 | h2719
                            · linarith only [h2719, hlam, p2674_0]
                            · rcases p2674_3 (m.d 1 2) (by simp) with h2721 | h2721
                              · rcases p2674_3 (m.d 1 3) (by simp) with h2722 | h2722
                                · rcases p2674_3 (m.d 1 4) (by simp) with h2723 | h2723
                                  · rcases p2674_3 (m.d 1 5) (by simp) with h2724 | h2724
                                    · rcases h5bigk with h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c | h2725c
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [hlam, p2725_0]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h1241, hlam, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2661, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2725_1, u2ehi4]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h1489, h2661, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h1489, h2661, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h1241, hc01, hc15, hlam, hphi, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [hlam, p2725_0]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2665, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2725_1, u2ehi4]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        rcases p2725_3 (m.d 0 5) (by simp) with h2734 | h2734
                                        · linarith only [h1241, h2734, hlam]
                                        · linarith only [h2661, h2734, hlam]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        rcases p2725_3 (m.d 0 5) (by simp) with h2737 | h2737
                                        · linarith only [h1241, h2737, hlam]
                                        · linarith only [h2662, h2737, hlam]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h1488, hlam, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2665, hlam, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [hlam, p2725_0]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h0, h1488, h2673, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h1488, h1489, h2661, h2663, h2666, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2661, hlam, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2667, hlam, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2671, hlam, p2725_0]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [hlam, p2725_0]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h1489, h2661, h2663, h2666, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2662, hlam, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2668, hlam, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2672, hlam, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [h2673, hlam, p2725_1]
                                      · have p2725_0 := h2725c.1
                                        have p2725_1 := h2725c.2.1
                                        have p2725_2 := h2725c.2.2.1
                                        have p2725_3 := h2725c.2.2.2
                                        linarith only [hlam, p2725_0]
                                    · linarith only [h2724, hlam, p2674_0]
                                  · linarith only [h2668, h2723, hlam, p2674_1]
                                · linarith only [h2722, h927, hlam]
                              · linarith only [h0, h2721, hlam]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h2665, hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h2667, hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [h2668, hlam, p2674_0]
                          · have p2674_0 := h2674c.1
                            have p2674_1 := h2674c.2.1
                            have p2674_2 := h2674c.2.2.1
                            have p2674_3 := h2674c.2.2.2
                            linarith only [hlam, p2674_0]
                        · linarith only [h1486, h1489, h2673, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h1489, h2661, h2662, h2663, h2666, h2672, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                    · linarith only [h1489, h2661, h2663, h2666, h2671, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h1489, h2661, h2662, h2666, h2668, hlam]
              · linarith only [h1489, h2661, h2666, h2667, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2768 | h2768
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2769 | h2769
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2770 | h2770
                  · linarith only [h1486, h2666, h2770, h927, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2772 | h2772
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2773 | h2773
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2774 | h2774
                        · rcases h1bigk with h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c | h2775c
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h0, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h927, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h1241, h1489, h2661, h2664, h2770, h2772, hc34, hlam, hphi, ht23, p2775_1, u2ehi4]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h1241, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            rcases p2775_3 (m.d 0 1) (by simp) with h2781 | h2781
                            · linarith only [h2781, hlam, p2775_0]
                            · rcases p2775_3 (m.d 1 2) (by simp) with h2783 | h2783
                              · rcases p2775_3 (m.d 1 3) (by simp) with h2784 | h2784
                                · linarith only [h2663, h2784, hlam]
                                · linarith only [h2784, h927, hlam]
                              · linarith only [h2783, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h1241, h2768, hc01, hc12, hlam, hphi, p2775_1]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h2666, h927, hc01, hc12, hlam, hphi, p2775_1]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h1241, hc01, hc12, hlam, hphi, p2775_1]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h2666, hc01, hc34, hlam, hphi, ht12, ht23, p2775_1]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h2663, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h2666, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h1241, h1488, h2666, hc34, hlam, hphi, ht23, p2775_1, u2ehi4]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            rcases p2775_3 (m.d 0 1) (by simp) with h2797 | h2797
                            · linarith only [h2797, hlam, p2775_0]
                            · rcases p2775_3 (m.d 1 2) (by simp) with h2799 | h2799
                              · rcases p2775_3 (m.d 1 3) (by simp) with h2800 | h2800
                                · linarith only [h2666, h2800, hlam]
                                · linarith only [h2800, h927, hlam]
                              · linarith only [h0, h2799, hlam]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h2664, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h927, hc01, hc14, hlam, hphi, p2775_1]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h1241, h2666, hc01, hc34, hlam, hphi, ht12, ht23, p2775_1]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h2666, h2768, hc01, hc34, hlam, hphi, ht12, ht23, p2775_1]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h2665, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h2768, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [h2769, hlam, p2775_0]
                          · have p2775_0 := h2775c.1
                            have p2775_1 := h2775c.2.1
                            have p2775_2 := h2775c.2.2.1
                            have p2775_3 := h2775c.2.2.2
                            linarith only [hlam, p2775_0]
                        · linarith only [h2666, h2774, h927, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h1489, h2661, h2662, h2773, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h2661, h2666, h2772, h927, hc23, hc34, hlam, hphi]
                · linarith only [h2661, h2662, h2664, h2666, h2769, h927, hc34, hlam, hphi, ht23, u2ehi3]
              · linarith only [h2661, h2768, h927, hlam]
          · linarith only [h0, h1486, h2665, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h1486, h2664, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1486, h2663, hlam]
    · linarith only [h1489, h2661, h2662, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h2822 | h2822
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2823 | h2823
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2824 | h2824
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2825 | h2825
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2826 | h2826
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2827 | h2827
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2828 | h2828
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2829 | h2829
                  · linarith only [h1486, h1487, h1489, h2661, h2829, hc35, hlam, hphi, ht23, u2ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2831 | h2831
                    · linarith only [h1486, h2661, h2831, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2833 | h2833
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2834 | h2834
                        · rcases h1bigk with h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c | h2835c
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h0, hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h927, hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h1486, h2661, h2827, h2828, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2835_1, u2ehi2]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h1241, hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            rcases p2835_3 (m.d 0 1) (by simp) with h2841 | h2841
                            · linarith only [h2841, hlam, p2835_0]
                            · rcases p2835_3 (m.d 1 2) (by simp) with h2843 | h2843
                              · rcases p2835_3 (m.d 1 3) (by simp) with h2844 | h2844
                                · linarith only [h2823, h2844, hlam]
                                · linarith only [h2844, h927, hlam]
                              · linarith only [h2843, hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h927, hc01, hc12, hlam, hphi, p2835_1]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h1486, h2661, h2827, h2828, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2835_1, u2ehi2]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h1486, h2661, h2827, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2835_1, u2ehi2]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            rcases p2835_3 (m.d 0 1) (by simp) with h2852 | h2852
                            · linarith only [h2852, hlam, p2835_0]
                            · rcases p2835_3 (m.d 1 2) (by simp) with h2854 | h2854
                              · rcases p2835_3 (m.d 1 3) (by simp) with h2855 | h2855
                                · rcases p2835_3 (m.d 1 4) (by simp) with h2856 | h2856
                                  · linarith only [h2826, h2856, hlam]
                                  · linarith only [h1486, h2661, h2827, h2828, h2856, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2835_1, u2ehi2]
                                · linarith only [h2855, hlam, p2835_0]
                              · linarith only [h0, h2854, hlam]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h2823, hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h1486, h2661, h2823, h2827, h2828, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2835_1, u2ehi2]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h1486, h2661, h2823, h2827, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2835_1, u2ehi2]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            rcases p2835_3 (m.d 0 1) (by simp) with h2865 | h2865
                            · linarith only [h2865, hlam, p2835_0]
                            · rcases p2835_3 (m.d 1 2) (by simp) with h2867 | h2867
                              · rcases p2835_3 (m.d 1 3) (by simp) with h2868 | h2868
                                · rcases p2835_3 (m.d 1 4) (by simp) with h2869 | h2869
                                  · rcases p2835_3 (m.d 1 5) (by simp) with h2870 | h2870
                                    · linarith only [h2828, h2870, hlam]
                                    · linarith only [h1241, h2870, hlam]
                                  · linarith only [h2869, hlam, p2835_0]
                                · linarith only [h2868, h927, hlam]
                              · linarith only [h0, h2867, hlam]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h2824, hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h2826, hlam, p2835_1]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h1486, h2661, h2827, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2835_1, u2ehi2]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            rcases p2835_3 (m.d 0 1) (by simp) with h2880 | h2880
                            · linarith only [h2880, hlam, p2835_0]
                            · rcases p2835_3 (m.d 1 2) (by simp) with h2882 | h2882
                              · rcases p2835_3 (m.d 1 3) (by simp) with h2883 | h2883
                                · rcases p2835_3 (m.d 1 4) (by simp) with h2884 | h2884
                                  · rcases p2835_3 (m.d 1 5) (by simp) with h2885 | h2885
                                    · rcases h5bigk with h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c | h2886c
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [hlam, p2886_0]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h1241, hlam, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2822, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2886_1, u2ehi4]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2661, hlam, p2886_0]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2661, h2823, h2826, h2834, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h1241, h2825, hc01, hc12, hlam, hphi, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [hlam, p2886_0]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2825, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2886_1, u2ehi4]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h1486, h2661, h2823, h2827, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2886_1, u2ehi2]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        rcases p2886_3 (m.d 0 5) (by simp) with h2896 | h2896
                                        · linarith only [h1241, h2896, hlam]
                                        · linarith only [h2822, h2896, hlam]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h1488, hlam, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2825, hlam, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [hlam, p2886_0]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2831, hlam, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h0, h1487, h2833, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h1488, hc35, hlam, hphi, ht23, p2886_1, u2ehi4]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2827, hlam, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2823, h2827, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2886_1, u2ehi4]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [hlam, p2886_0]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2823, h2826, h2834, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2822, hlam, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2828, hlam, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2833, hlam, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [h2834, hlam, p2886_1]
                                      · have p2886_0 := h2886c.1
                                        have p2886_1 := h2886c.2.1
                                        have p2886_2 := h2886c.2.2.1
                                        have p2886_3 := h2886c.2.2.2
                                        linarith only [hlam, p2886_0]
                                    · linarith only [h2885, hlam, p2835_0]
                                  · linarith only [h2828, h2884, hlam, p2835_1]
                                · linarith only [h2883, h927, hlam]
                              · linarith only [h0, h2882, hlam]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h2825, hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h2827, hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [h2828, hlam, p2835_0]
                          · have p2835_0 := h2835c.1
                            have p2835_1 := h2835c.2.1
                            have p2835_2 := h2835c.2.2.1
                            have p2835_3 := h2835c.2.2.2
                            linarith only [hlam, p2835_0]
                        · linarith only [h1486, h1489, h2834, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h1489, h2822, h2823, h2826, h2833, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · linarith only [h1489, h2822, h2823, h2824, h2826, h2828, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
              · linarith only [h1489, h2826, h2827, h927, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2926 | h2926
              · linarith only [h1486, h2661, h2826, h2926, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2928 | h2928
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2929 | h2929
                  · linarith only [h1486, h2826, h2929, h927, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2931 | h2931
                    · linarith only [h1486, h2926, h2931, h927, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2933 | h2933
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2934 | h2934
                        · rcases h1bigk with h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c | h2935c
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h0, hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h927, hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h0, h1241, h1486, h2661, h2928, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2935_1, u2ehi2]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h1241, hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            rcases p2935_3 (m.d 0 1) (by simp) with h2941 | h2941
                            · linarith only [h2941, hlam, p2935_0]
                            · rcases p2935_3 (m.d 1 2) (by simp) with h2943 | h2943
                              · rcases p2935_3 (m.d 1 3) (by simp) with h2944 | h2944
                                · linarith only [h2823, h2944, hlam]
                                · linarith only [h2944, h927, hlam]
                              · linarith only [h2943, hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h927, hc01, hc12, hlam, hphi, p2935_1]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h2826, h927, hc01, hc12, hlam, hphi, p2935_1]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h1241, hc01, hc12, hlam, hphi, p2935_1]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h2926, h2934, hc01, hc34, hlam, hphi, ht12, ht23, p2935_1]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h2823, hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h2826, hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h2926, hlam, p2935_1]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            rcases p2935_3 (m.d 0 1) (by simp) with h2957 | h2957
                            · linarith only [h2957, hlam, p2935_0]
                            · rcases p2935_3 (m.d 1 2) (by simp) with h2959 | h2959
                              · rcases p2935_3 (m.d 1 3) (by simp) with h2960 | h2960
                                · linarith only [h2826, h2960, hlam]
                                · linarith only [h2960, h927, hlam]
                              · linarith only [h0, h2959, hlam]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h2824, hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h927, hc01, hc14, hlam, hphi, p2935_1]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h2826, h2926, h927, hc01, hc34, hlam, hphi, ht12, ht23, p2935_1]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            rcases p2935_3 (m.d 0 1) (by simp) with h2968 | h2968
                            · linarith only [h2968, hlam, p2935_0]
                            · rcases p2935_3 (m.d 1 2) (by simp) with h2970 | h2970
                              · rcases p2935_3 (m.d 1 3) (by simp) with h2971 | h2971
                                · linarith only [h2926, h2971, hlam]
                                · linarith only [h2971, h927, hlam]
                              · linarith only [h0, h2970, hlam]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h2825, hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h927, hc01, hc15, hlam, hphi, p2935_1]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [h2928, hlam, p2935_0]
                          · have p2935_0 := h2935c.1
                            have p2935_1 := h2935c.2.1
                            have p2935_2 := h2935c.2.2.1
                            have p2935_3 := h2935c.2.2.2
                            linarith only [hlam, p2935_0]
                        · linarith only [h1487, h1489, h2933, h2934, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1489, h2822, h2933, hc34, hlam, hphi, ht23, u2ehi3]
                · linarith only [h1489, h2822, h2824, h2928, hc34, hlam, hphi, ht23, u2ehi3]
          · linarith only [h0, h1488, h2825, hlam]
        · linarith only [h0, h1488, h2824, hc24, hlam, hphi, u2ehi4]
      · linarith only [h0, h1486, h2823, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h2985 | h2985
      · rcases m.htr 1 2 4 (by decide) (by decide) with h2986 | h2986
        · rcases m.htr 1 2 5 (by decide) (by decide) with h2987 | h2987
          · rcases m.htr 1 3 4 (by decide) (by decide) with h2988 | h2988
            · rcases m.htr 1 3 5 (by decide) (by decide) with h2989 | h2989
              · rcases m.htr 1 4 5 (by decide) (by decide) with h2990 | h2990
                · rcases m.htr 2 3 4 (by decide) (by decide) with h2991 | h2991
                  · linarith only [h1486, h1489, h2991, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h2993 | h2993
                    · linarith only [h1486, h2661, h2993, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h2995 | h2995
                      · linarith only [h1486, h1487, h1489, h2822, h2995, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h2997 | h2997
                        · linarith only [h1486, h1489, h2822, h2997, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h1486, h1489, h2990, h2997, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h1486, h1489, h2988, h2990, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h1486, h1489, h2988, h2989, hc35, hlam, hphi, ht23, u2ehi2]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3002 | h3002
              · linarith only [h1486, h2661, h2988, h3002, hc34, hlam, hphi, ht23, u2ehi2]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h3004 | h3004
                · linarith only [h1486, h1489, h2822, h2988, h3004, hc34, hlam, hphi, ht23, u2ehi2]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h3006 | h3006
                  · linarith only [h1486, h1489, h3006, hlam]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h3008 | h3008
                    · linarith only [h1486, h2661, h3008, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h3010 | h3010
                      · linarith only [h1486, h2988, h3004, h3010, h927, hc24, hlam, hphi, u2ehi2]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h3012 | h3012
                        · linarith only [h1486, h2988, h3004, h3012, h927, hc34, hlam, hphi, ht23, u2ehi2]
                        · linarith only [h1486, h1489, h3012, hc45, hlam, hphi, ht23, ht34, u2ehi2]
          · linarith only [h0, h1486, h2987, hc25, hlam, hphi, u2ehi2]
        · linarith only [h0, h1487, h2986, hlam]
      · linarith only [h0, h1486, h2985, hlam]

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1488 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h1489 | h1489
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487 h1488 h1489
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487 h1488 h1489

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h1488 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  linarith only [h1486, h1488, hc25, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h1488 | h1488
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487 h1488
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487 h1488

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h1487 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  linarith only [h1486, h1487, hc24, hlam, hphi, u2ehi2]

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h1487 | h1487
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x0 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0_x1 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486 h1487

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h1486 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h3020 | h3020
  · linarith only [h1486, h3020, hc23, hlam, hphi, u2ehi3]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h3022 | h3022
    · linarith only [h1486, h3022, hc23, hlam, hphi, u2ehi4]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h3024 | h3024
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3025 | h3025
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3026 | h3026
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3027 | h3027
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3028 | h3028
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3029 | h3029
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3030 | h3030
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3031 | h3031
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3032 | h3032
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3033 | h3033
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3034 | h3034
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3035 | h3035
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3036 | h3036
                              · rcases h1bigk with h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c | h3037c
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h0, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h927, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3022, h3029, h3032, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3037_1, u2ehi0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h1241, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  rcases p3037_3 (m.d 0 1) (by simp) with h3043 | h3043
                                  · linarith only [h3043, hlam, p3037_0]
                                  · rcases p3037_3 (m.d 1 2) (by simp) with h3045 | h3045
                                    · rcases p3037_3 (m.d 1 3) (by simp) with h3046 | h3046
                                      · linarith only [h3027, h3046, hlam]
                                      · linarith only [h3046, h927, hlam]
                                    · linarith only [h3045, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3022, h3029, h3030, h3032, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3037_1, u2ehi0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3022, h3029, h3032, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3037_1, u2ehi0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3022, h3029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3037_1, u2ehi0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  rcases p3037_3 (m.d 0 1) (by simp) with h3054 | h3054
                                  · linarith only [h3054, hlam, p3037_0]
                                  · rcases p3037_3 (m.d 1 2) (by simp) with h3056 | h3056
                                    · rcases p3037_3 (m.d 1 3) (by simp) with h3057 | h3057
                                      · rcases p3037_3 (m.d 1 4) (by simp) with h3058 | h3058
                                        · linarith only [h3030, h3058, hlam]
                                        · linarith only [h3022, h3029, h3032, h3058, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3037_1, u2ehi0]
                                      · linarith only [h3057, hlam, p3037_0]
                                    · linarith only [h0, h3056, hlam]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3027, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3022, h3029, h3032, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3037_1, u2ehi0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3022, h3027, h3029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3037_1, u2ehi0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  rcases p3037_3 (m.d 0 1) (by simp) with h3067 | h3067
                                  · linarith only [h3067, hlam, p3037_0]
                                  · rcases p3037_3 (m.d 1 2) (by simp) with h3069 | h3069
                                    · rcases p3037_3 (m.d 1 3) (by simp) with h3070 | h3070
                                      · rcases p3037_3 (m.d 1 4) (by simp) with h3071 | h3071
                                        · rcases p3037_3 (m.d 1 5) (by simp) with h3072 | h3072
                                          · linarith only [h3032, h3072, hlam]
                                          · linarith only [h1241, h3072, hlam]
                                        · linarith only [h3071, hlam, p3037_0]
                                      · linarith only [h3070, h927, hlam]
                                    · linarith only [h0, h3069, hlam]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3028, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3030, hlam, p3037_1]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3022, h3029, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3037_1, u2ehi0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  rcases p3037_3 (m.d 0 1) (by simp) with h3082 | h3082
                                  · linarith only [h3082, hlam, p3037_0]
                                  · rcases p3037_3 (m.d 1 2) (by simp) with h3084 | h3084
                                    · rcases p3037_3 (m.d 1 3) (by simp) with h3085 | h3085
                                      · rcases p3037_3 (m.d 1 4) (by simp) with h3086 | h3086
                                        · rcases p3037_3 (m.d 1 5) (by simp) with h3087 | h3087
                                          · rcases h5bigk with h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [hlam, p3088_0]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h1241, hlam, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3022, hlam, p3088_0]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3020, h3026, h3027, h3033, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3020, h3026, h3027, h3033, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h1241, hc01, hc15, hlam, hphi, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [hlam, p3088_0]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3022, h3029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3088_1, u2ehi0]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              rcases p3088_3 (m.d 0 5) (by simp) with h3097 | h3097
                                              · linarith only [h1241, h3097, hlam]
                                              · linarith only [h3025, h3097, hlam]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              rcases p3088_3 (m.d 0 5) (by simp) with h3100 | h3100
                                              · linarith only [h1241, h3100, hlam]
                                              · linarith only [h3026, h3100, hlam]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3022, hc25, hlam, hphi, p3088_1, u2ehi0]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3029, hlam, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [hlam, p3088_0]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3027, h3034, h3036, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3027, h3033, h3035, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3025, hlam, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3031, hlam, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3034, hlam, p3088_0]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [hlam, p3088_0]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3025, hc03, hc45, hlam, hphi, ht0b, ht5b, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3026, hlam, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3032, hlam, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3035, hlam, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [h3036, hlam, p3088_1]
                                            · have p3088_0 := h3088c.1
                                              have p3088_1 := h3088c.2.1
                                              have p3088_2 := h3088c.2.2.1
                                              have p3088_3 := h3088c.2.2.2
                                              linarith only [hlam, p3088_0]
                                          · linarith only [h3087, hlam, p3037_0]
                                        · linarith only [h3032, h3086, hlam, p3037_1]
                                      · linarith only [h3085, h927, hlam]
                                    · linarith only [h0, h3084, hlam]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3029, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3031, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [h3032, hlam, p3037_0]
                                · have p3037_0 := h3037c.1
                                  have p3037_1 := h3037c.2.1
                                  have p3037_2 := h3037c.2.2.1
                                  have p3037_3 := h3037c.2.2.2
                                  linarith only [hlam, p3037_0]
                              · rcases h1bigk with h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c | h3126c
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h0, hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h927, hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h0, h3028, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3126_1, u2ehi3]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h1241, hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  rcases p3126_3 (m.d 0 1) (by simp) with h3132 | h3132
                                  · linarith only [h3132, hlam, p3126_0]
                                  · rcases p3126_3 (m.d 1 2) (by simp) with h3134 | h3134
                                    · rcases p3126_3 (m.d 1 3) (by simp) with h3135 | h3135
                                      · linarith only [h3027, h3135, hlam]
                                      · linarith only [h3135, h927, hlam]
                                    · linarith only [h3134, hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h927, hc01, hc12, hlam, hphi, p3126_1]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3020, h3026, h3028, h3036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3126_1]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3022, h3029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3126_1, u2ehi0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  rcases p3126_3 (m.d 0 1) (by simp) with h3143 | h3143
                                  · linarith only [h3143, hlam, p3126_0]
                                  · rcases p3126_3 (m.d 1 2) (by simp) with h3145 | h3145
                                    · rcases p3126_3 (m.d 1 3) (by simp) with h3146 | h3146
                                      · rcases p3126_3 (m.d 1 4) (by simp) with h3147 | h3147
                                        · linarith only [h3030, h3147, hlam]
                                        · linarith only [h0, h3022, h3029, h3032, h3147, hlam]
                                      · linarith only [h3146, hlam, p3126_0]
                                    · linarith only [h0, h3145, hlam]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3027, hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3022, h3029, h3032, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3126_1, u2ehi0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3022, h3027, h3029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3126_1, u2ehi0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  rcases p3126_3 (m.d 0 1) (by simp) with h3156 | h3156
                                  · linarith only [h3156, hlam, p3126_0]
                                  · rcases p3126_3 (m.d 1 2) (by simp) with h3158 | h3158
                                    · rcases p3126_3 (m.d 1 3) (by simp) with h3159 | h3159
                                      · rcases p3126_3 (m.d 1 4) (by simp) with h3160 | h3160
                                        · rcases p3126_3 (m.d 1 5) (by simp) with h3161 | h3161
                                          · linarith only [h3032, h3161, hlam]
                                          · linarith only [h1241, h3161, hlam]
                                        · linarith only [h3160, hlam, p3126_0]
                                      · linarith only [h3159, h927, hlam]
                                    · linarith only [h0, h3158, hlam]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3028, hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3030, hlam, p3126_1]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3022, h3029, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3126_1, u2ehi0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  rcases p3126_3 (m.d 0 1) (by simp) with h3171 | h3171
                                  · linarith only [h3171, hlam, p3126_0]
                                  · rcases p3126_3 (m.d 1 2) (by simp) with h3173 | h3173
                                    · rcases p3126_3 (m.d 1 3) (by simp) with h3174 | h3174
                                      · rcases p3126_3 (m.d 1 4) (by simp) with h3175 | h3175
                                        · rcases p3126_3 (m.d 1 5) (by simp) with h3176 | h3176
                                          · rcases h5bigk with h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c | h3177c
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [hlam, p3177_0]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h1241, hlam, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3022, hlam, p3177_0]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h1486, h3025, h3027, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h1486, h3024, h3026, h3027, h3036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h1241, hc01, hc15, hlam, hphi, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [hlam, p3177_0]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3022, h3029, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3177_1, u2ehi0]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              rcases p3177_3 (m.d 0 5) (by simp) with h3186 | h3186
                                              · linarith only [h1241, h3186, hlam]
                                              · linarith only [h3025, h3186, hlam]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3027, h3030, h3032, h3036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3022, h3035, hc24, hlam, hphi, p3177_1, u2ehi0]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3029, hlam, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [hlam, p3177_0]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3027, h3033, h3035, h3036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3027, h3033, h3035, h3036, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3025, hlam, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3031, hlam, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3034, hlam, p3177_0]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [hlam, p3177_0]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3036, hlam, p3177_0]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3026, hlam, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3032, hlam, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3035, hlam, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [h3036, hc34, hc45, hlam, hphi, p3177_1]
                                            · have p3177_0 := h3177c.1
                                              have p3177_1 := h3177c.2.1
                                              have p3177_2 := h3177c.2.2.1
                                              have p3177_3 := h3177c.2.2.2
                                              linarith only [hlam, p3177_0]
                                          · linarith only [h3176, hlam, p3126_0]
                                        · linarith only [h3032, h3175, hlam, p3126_1]
                                      · linarith only [h3174, h927, hlam]
                                    · linarith only [h0, h3173, hlam]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3029, hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3031, hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [h3032, hlam, p3126_0]
                                · have p3126_0 := h3126c.1
                                  have p3126_1 := h3126c.2.1
                                  have p3126_2 := h3126c.2.2.1
                                  have p3126_3 := h3126c.2.2.2
                                  linarith only [hlam, p3126_0]
                            · linarith only [h3020, h3035, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1486, h3034, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1486, h3033, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h3020, h3024, h3026, h3028, h3032, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h1486, h3025, h3031, h927, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h1486, h3024, h3027, h3030, hlam]
                · linarith only [h3027, h3029, hc25, hlam, hphi, u2ehi2]
              · linarith only [h1486, h3027, h3028, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3221 | h3221
              · linarith only [h3027, h3221, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3223 | h3223
                · linarith only [h3027, h3223, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3225 | h3225
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3226 | h3226
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3227 | h3227
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3228 | h3228
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3229 | h3229
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3230 | h3230
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h3231 | h3231
                              · rcases h1bigk with h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c | h3232c
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [hlam, p3232_0]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h0, hlam, p3232_0]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h927, hlam, p3232_0]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h0, h3223, h3227, hlam, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h1241, hlam, p3232_0]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h3027, hc01, hc23, hlam, hphi, ht12, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [hlam, p3232_0]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h3027, hlam, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h3221, hlam, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h3223, hlam, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  rcases p3232_3 (m.d 0 1) (by simp) with h3243 | h3243
                                  · linarith only [h3243, hlam, p3232_0]
                                  · rcases p3232_3 (m.d 1 2) (by simp) with h3245 | h3245
                                    · linarith only [h3027, h3245, hlam]
                                    · linarith only [h0, h3245, hlam]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h3027, hc23, hlam, hphi, p3232_1, u2ehi1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [hlam, p3232_0]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h0, h3027, h3223, h3227, hc01, hc23, hlam, hphi, ht12, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h0, h3027, h3223, hc01, hc23, hlam, hphi, ht12, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  rcases p3232_3 (m.d 0 1) (by simp) with h3252 | h3252
                                  · linarith only [h3252, hlam, p3232_0]
                                  · rcases p3232_3 (m.d 1 2) (by simp) with h3254 | h3254
                                    · linarith only [h3221, h3254, hlam]
                                    · linarith only [h0, h3254, hlam]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h3225, hlam, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [hlam, p3232_0]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h0, h3221, h3223, h3228, hc01, hc23, hlam, hphi, ht12, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  rcases p3232_3 (m.d 0 1) (by simp) with h3261 | h3261
                                  · linarith only [h3261, hlam, p3232_0]
                                  · rcases p3232_3 (m.d 1 2) (by simp) with h3263 | h3263
                                    · linarith only [h3223, h3263, hlam]
                                    · linarith only [h0, h3263, hlam]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h0, hc01, hc15, hlam, hphi, p3232_1]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h3226, hlam, p3232_0]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [h3227, hlam, p3232_0]
                                · have p3232_0 := h3232c.1
                                  have p3232_1 := h3232c.2.1
                                  have p3232_2 := h3232c.2.2.1
                                  have p3232_3 := h3232c.2.2.2
                                  linarith only [hlam, p3232_0]
                              · rcases h1bigk with h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c | h3270c
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [hlam, p3270_0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h0, hlam, p3270_0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h927, hlam, p3270_0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h0, h3027, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h1241, hlam, p3270_0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h3027, hc01, hc23, hlam, hphi, ht12, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [hlam, p3270_0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h3027, hlam, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h3221, hlam, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h3223, hlam, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  rcases p3270_3 (m.d 0 1) (by simp) with h3281 | h3281
                                  · linarith only [h3281, hlam, p3270_0]
                                  · rcases p3270_3 (m.d 1 2) (by simp) with h3283 | h3283
                                    · linarith only [h3027, h3283, hlam]
                                    · linarith only [h0, h3283, hlam]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h0, h3027, hc01, hc23, hlam, hphi, ht12, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [hlam, p3270_0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h3027, h3227, h3231, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h1241, h3022, h3027, hc23, hlam, hphi, p3270_1, u2ehi0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  rcases p3270_3 (m.d 0 1) (by simp) with h3290 | h3290
                                  · linarith only [h3290, hlam, p3270_0]
                                  · rcases p3270_3 (m.d 1 2) (by simp) with h3292 | h3292
                                    · linarith only [h3221, h3292, hlam]
                                    · linarith only [h0, h3292, hlam]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h3225, hlam, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [hlam, p3270_0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h1241, h3022, h3221, hc24, hlam, hphi, p3270_1, u2ehi0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  rcases p3270_3 (m.d 0 1) (by simp) with h3299 | h3299
                                  · linarith only [h3299, hlam, p3270_0]
                                  · rcases p3270_3 (m.d 1 2) (by simp) with h3301 | h3301
                                    · linarith only [h3223, h3301, hlam]
                                    · linarith only [h0, h3301, hlam]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h0, hc01, hc15, hlam, hphi, p3270_1]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h3226, hlam, p3270_0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [h3227, hlam, p3270_0]
                                · have p3270_0 := h3270c.1
                                  have p3270_1 := h3270c.2.1
                                  have p3270_2 := h3270c.2.2.1
                                  have p3270_3 := h3270c.2.2.2
                                  linarith only [hlam, p3270_0]
                            · linarith only [h3024, h3026, h3027, h3230, h927, hc23, hlam, hphi, u2ehi3]
                          · linarith only [h1241, h3025, h3027, h3225, h3227, h3229, hlam]
                        · linarith only [h0, h3027, h3228, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h3024, h3026, h3221, h3227, h927, hc01, hc13, hlam, hphi]
                    · linarith only [h3025, h3226, h927, hlam]
                  · linarith only [h3024, h3225, h927, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3314 | h3314
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3315 | h3315
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3316 | h3316
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3317 | h3317
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3318 | h3318
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3319 | h3319
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3320 | h3320
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3321 | h3321
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3322 | h3322
                            · linarith only [h3020, h3026, h3322, hc24, hlam, hphi, u2ehi0]
                            · linarith only [h3020, h3314, h3317, h3319, h3322, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1486, h3025, h3321, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h3024, h3026, h3314, h3317, h3319, h3320, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h3020, h3315, h3319, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h3020, h3025, h3315, h3317, h3318, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                  · linarith only [h3024, h3317, h927, hlam]
                · linarith only [h3314, h3316, hc25, hlam, hphi, u2ehi2]
              · linarith only [h1486, h3314, h3315, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3332 | h3332
              · linarith only [h3314, h3332, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3334 | h3334
                · linarith only [h3314, h3334, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3336 | h3336
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3337 | h3337
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3338 | h3338
                      · linarith only [h3020, h3026, h3332, h3338, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3340 | h3340
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3341 | h3341
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h3342 | h3342
                            · linarith only [h0, h3332, h3338, h3340, h3342, hc01, hc23, hlam, hphi, ht12]
                            · linarith only [h3020, h3342, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                          · linarith only [h1486, h3341, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h3024, h3314, h3340, h927, hlam]
                    · linarith only [h3025, h3337, h927, hlam]
                  · linarith only [h3024, h3336, h927, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3349 | h3349
          · linarith only [h3024, h3025, h3349, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3351 | h3351
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3352 | h3352
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3353 | h3353
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3354 | h3354
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3355 | h3355
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3356 | h3356
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3357 | h3357
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3358 | h3358
                          · linarith only [h3020, h3024, h3025, h3351, h3358, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                          · linarith only [h1486, h3358, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h1486, h3024, h3357, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h3020, h3352, h3356, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1486, h3351, h3355, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1486, h3024, h3025, h3351, h3354, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1486, h3351, h3353, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1486, h3351, h3352, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3367 | h3367
              · linarith only [h3351, h3367, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3369 | h3369
                · linarith only [h3351, h3369, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3371 | h3371
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3372 | h3372
                    · linarith only [h1486, h3025, h3351, h3372, hc23, hlam, hphi, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3374 | h3374
                      · linarith only [h3020, h3349, h3371, h3372, h3374, hc35, hlam, hphi, ht23, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3376 | h3376
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h3377 | h3377
                          · linarith only [h3367, h3371, h3372, h3377, hc23, hlam, hphi, u2ehi1]
                          · linarith only [h1486, h3377, hc35, hlam, hphi, ht23, u2ehi0]
                        · linarith only [h0, h3024, h3351, h3376, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · linarith only [h3024, h3025, h3371, hc13, hc35, hlam, hphi]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3382 | h3382
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3383 | h3383
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3384 | h3384
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3385 | h3385
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3386 | h3386
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3387 | h3387
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3388 | h3388
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3389 | h3389
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3390 | h3390
                        · linarith only [h3024, h3382, h3384, h3390, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h1486, h3387, h3390, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h3020, h3022, h3024, h3382, h3383, h3387, h3389, hc24, hlam, hphi, u2ehi0]
                    · linarith only [h3024, h3382, h3388, hc13, hc34, hlam, hphi]
                  · linarith only [h1486, h3384, h3387, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h3385, h3386, hc25, hlam, hphi, u2ehi3]
              · linarith only [h1486, h3384, h3385, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3398 | h3398
              · linarith only [h3384, h3398, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3400 | h3400
                · linarith only [h3384, h3400, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3402 | h3402
                  · linarith only [h1486, h3024, h3384, h3402, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3404 | h3404
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3405 | h3405
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3406 | h3406
                        · linarith only [h3022, h3382, h3402, h3406, h927, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1486, h3406, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h3022, h3024, h3382, h3383, h3402, h3405, h927, hc34, hlam, hphi, ht23, u2ehi0]
                    · linarith only [h3382, h3404, h927, hlam]
          · linarith only [h3024, h3382, h3383, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h3412 | h3412
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3413 | h3413
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3414 | h3414
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3415 | h3415
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3416 | h3416
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3417 | h3417
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3418 | h3418
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3419 | h3419
                        · linarith only [h1486, h3024, h3419, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1486, h3413, h3416, h3419, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · linarith only [h3020, h3412, h3414, h3418, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                    · linarith only [h3024, h3416, h3417, hc03, hc35, hlam, hphi]
                  · linarith only [h1486, h3413, h3416, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1486, h3413, h3415, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1486, h3413, h3414, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3427 | h3427
              · linarith only [h3413, h3427, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3429 | h3429
                · linarith only [h3413, h3429, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3431 | h3431
                  · linarith only [h1486, h3024, h3413, h3431, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3433 | h3433
                    · linarith only [h1486, h3382, h3431, h3433, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3435 | h3435
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3436 | h3436
                        · linarith only [h3413, h3431, h3436, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h1486, h3436, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h0, h3024, h3412, h3427, h3435, hc01, hc34, hlam, hphi, ht12, ht23]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h3440 | h3440
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3441 | h3441
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3442 | h3442
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3443 | h3443
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3444 | h3444
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3445 | h3445
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3446 | h3446
                        · linarith only [h1486, h3024, h3440, h3446, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                        · linarith only [h1486, h3446, hc34, hlam, hphi, ht23, u2ehi0]
                      · linarith only [h3020, h3441, h3445, hc45, hlam, hphi, ht23, ht34, u2ehi0]
                    · linarith only [h1486, h3440, h3444, hc35, hlam, hphi, ht23, u2ehi0]
                  · linarith only [h1486, h3440, h3443, hc34, hlam, hphi, ht23, u2ehi0]
                · linarith only [h1486, h3440, h3442, hc25, hlam, hphi, u2ehi0]
              · linarith only [h1486, h3440, h3441, hc24, hlam, hphi, u2ehi0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h3454 | h3454
              · linarith only [h3440, h3454, hc23, hlam, hphi, u2ehi3]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h3456 | h3456
                · linarith only [h3440, h3456, hc23, hlam, hphi, u2ehi4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h3458 | h3458
                  · linarith only [h1486, h3024, h3440, h3458, hc23, hlam, hphi, u2ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h3460 | h3460
                    · linarith only [h1486, h3382, h3458, h3460, hc34, hlam, hphi, ht23, u2ehi0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h3462 | h3462
                      · linarith only [h3020, h3412, h3454, h3462, hc24, hlam, hphi, u2ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h3464 | h3464
                        · linarith only [h1486, h3024, h3464, hc23, hlam, hphi, u2ehi0]
                        · linarith only [h1486, h3464, hc34, hlam, hphi, ht23, u2ehi0]

set_option maxHeartbeats 5080000 in
theorem r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h927 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1241 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h1486 | h1486
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x0 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486
  · exact r1l7_11_12_14_25_L_I_L_R_L_I_H_I_s0_x1_x1_x1 m hb1 hb2 hb4 hb5 hg0 h927 h1241 h1486

end R2N4
