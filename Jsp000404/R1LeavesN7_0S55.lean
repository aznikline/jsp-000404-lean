import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S53
import Jsp000404.R1LeavesN7_0S54

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19774000 in
set_option maxHeartbeats 19774000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h22010 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22011 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  rcases m.htr 0 3 5 (by decide) (by decide) with h22670 | h22670
  · rcases m.htr 0 4 5 (by decide) (by decide) with h22671 | h22671
    · rcases m.htr 1 2 3 (by decide) (by decide) with h22672 | h22672
      · linarith only [h0, h22010, h22672, h4, hc01, hc25, hlam, hphi, ht0b, ht5b]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h22674 | h22674
        · linarith only [h0, h19744, h22674, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h22676 | h22676
          · rcases m.htr 1 3 4 (by decide) (by decide) with h22677 | h22677
            · linarith only [h1, h22011, h22677, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h22679 | h22679
              · rcases m.htr 1 4 5 (by decide) (by decide) with h22680 | h22680
                · rcases m.htr 2 3 4 (by decide) (by decide) with h22681 | h22681
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h22682 | h22682
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h22683 | h22683
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h22684 | h22684
                        · rcases h1bigk with h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c | h22685c
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            rcases p22685_3 (m.d 0 1) (by simp) with h22687 | h22687
                            · rcases p22685_3 (m.d 1 2) (by simp) with h22688 | h22688
                              · linarith only [h22688, hlam, p22685_0]
                              · rcases p22685_3 (m.d 1 3) (by simp) with h22690 | h22690
                                · linarith only [h1, h22690, hlam]
                                · linarith only [h22672, h22690, hlam]
                            · linarith only [h22687, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            rcases p22685_3 (m.d 0 1) (by simp) with h22694 | h22694
                            · rcases p22685_3 (m.d 1 2) (by simp) with h22695 | h22695
                              · linarith only [h0, h22695, hlam]
                              · rcases p22685_3 (m.d 1 3) (by simp) with h22697 | h22697
                                · linarith only [h22697, hlam, p22685_0]
                                · rcases p22685_3 (m.d 1 4) (by simp) with h22699 | h22699
                                  · linarith only [h2, h22699, hlam]
                                  · linarith only [h22677, h22699, hlam]
                            · linarith only [h22694, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            rcases p22685_3 (m.d 0 1) (by simp) with h22703 | h22703
                            · rcases p22685_3 (m.d 1 2) (by simp) with h22704 | h22704
                              · linarith only [h0, h22704, hlam]
                              · rcases p22685_3 (m.d 1 3) (by simp) with h22706 | h22706
                                · linarith only [h1, h22706, hlam]
                                · rcases p22685_3 (m.d 1 4) (by simp) with h22708 | h22708
                                  · linarith only [h22708, hlam, p22685_0]
                                  · rcases p22685_3 (m.d 1 5) (by simp) with h22710 | h22710
                                    · linarith only [h22710, h3, hlam]
                                    · rcases h1emax with h22712 | h22712 | h22712 | h22712 | h22712
                                      · linarith only [h0, h22676, h22682, h22684, h22712, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                      · rcases h2bigk with h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c | h22714c
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22011, h22676, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22714_1]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h4, hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h19744, hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22011, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22714_1]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h0, hlam, p22714_1]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22672, hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22674, hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h0, h22011, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22714_1]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          rcases p22714_3 (m.d 0 2) (by simp) with h22725 | h22725
                                          · linarith only [h22725, hlam, p22714_0]
                                          · rcases p22714_3 (m.d 1 2) (by simp) with h22727 | h22727
                                            · linarith only [h22672, h22727, hlam]
                                            · rcases p22714_3 (m.d 2 3) (by simp) with h22729 | h22729
                                              · rcases p22714_3 (m.d 2 4) (by simp) with h22730 | h22730
                                                · linarith only [h22681, h22730, hlam]
                                                · linarith only [h19744, h22730, hlam]
                                              · linarith only [h22729, hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          rcases p22714_3 (m.d 0 2) (by simp) with h22734 | h22734
                                          · linarith only [h22734, h4, hlam]
                                          · linarith only [h0, h22734, hlam]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22011, h22681, h4, hc02, hc23, hlam, hphi, p22714_1]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h0, h22011, h22676, h22681, h4, hlam, p22714_2]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          rcases p22714_3 (m.d 0 2) (by simp) with h22740 | h22740
                                          · linarith only [h22740, hlam, p22714_0]
                                          · rcases p22714_3 (m.d 1 2) (by simp) with h22742 | h22742
                                            · linarith only [h22674, h22742, hlam]
                                            · rcases p22714_3 (m.d 2 3) (by simp) with h22744 | h22744
                                              · rcases p22714_3 (m.d 2 4) (by simp) with h22745 | h22745
                                                · rcases p22714_3 (m.d 2 5) (by simp) with h22746 | h22746
                                                  · linarith only [h22683, h22746, hlam]
                                                  · rcases h4bigk with h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c | h22748c
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22011, h22674, h22676, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22748_1]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h19744, hlam, p22748_1]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22011, hlam, p22748_1]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      rcases p22748_3 (m.d 0 4) (by simp) with h22753 | h22753
                                                      · rcases p22748_3 (m.d 1 4) (by simp) with h22754 | h22754
                                                        · linarith only [h2, h22754, hlam]
                                                        · linarith only [h22680, h22754, hlam]
                                                      · linarith only [h22753, hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h2, hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22674, hlam, p22748_1]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22677, hlam, p22748_1]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p22685_1, p22748_1]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      rcases p22748_3 (m.d 0 4) (by simp) with h22763 | h22763
                                                      · linarith only [h19744, h22763, hlam]
                                                      · rcases p22748_3 (m.d 1 4) (by simp) with h22765 | h22765
                                                        · linarith only [h22674, h22765, hlam]
                                                        · rcases p22748_3 (m.d 2 4) (by simp) with h22767 | h22767
                                                          · rcases p22748_3 (m.d 3 4) (by simp) with h22768 | h22768
                                                            · linarith only [h22681, h22768, hlam]
                                                            · linarith only [h22011, h22768, hlam]
                                                          · linarith only [h19744, h22767, hlam]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      rcases p22748_3 (m.d 0 4) (by simp) with h22772 | h22772
                                                      · linarith only [h19744, h22772, hlam]
                                                      · linarith only [h2, h22772, hlam]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h0, h22011, h22676, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22748_1]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h0, h22676, h22682, h22684, hlam, p22714_1, p22748_2]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h0, h22011, h22676, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22748_1]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22674, h22676, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22748_1]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22681, hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      rcases p22748_3 (m.d 0 4) (by simp) with h22782 | h22782
                                                      · linarith only [h22011, h22782, hlam]
                                                      · linarith only [h22671, h22782, hlam]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22671, hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22680, hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22683, hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [h22684, hlam, p22748_0]
                                                    · have p22748_0 := h22748c.1
                                                      have p22748_1 := h22748c.2.1
                                                      have p22748_2 := h22748c.2.2.1
                                                      have p22748_3 := h22748c.2.2.2
                                                      linarith only [hlam, p22748_0]
                                                · linarith only [h22745, hlam, p22714_0]
                                              · linarith only [h22744, h4, hlam]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          rcases p22714_3 (m.d 0 2) (by simp) with h22792 | h22792
                                          · linarith only [h19744, h22792, hlam]
                                          · linarith only [h0, h22792, hlam]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22681, hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          rcases p22714_3 (m.d 0 2) (by simp) with h22797 | h22797
                                          · linarith only [h19744, h22797, hlam]
                                          · linarith only [h22010, h22797, hlam]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22010, hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22676, hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22682, hlam, p22714_0]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [h22683, hlam, p22714_1]
                                        · have p22714_0 := h22714c.1
                                          have p22714_1 := h22714c.2.1
                                          have p22714_2 := h22714c.2.2.1
                                          have p22714_3 := h22714c.2.2.2
                                          linarith only [hlam, p22714_0]
                                      · rcases h2bigk with h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c | h22805c
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22676, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22805_1]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h4, hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h19744, hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22011, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22805_1]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h0, hlam, p22805_1]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22672, hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22674, hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h0, h22011, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22805_1]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          rcases p22805_3 (m.d 0 2) (by simp) with h22816 | h22816
                                          · linarith only [h22816, hlam, p22805_0]
                                          · rcases p22805_3 (m.d 1 2) (by simp) with h22818 | h22818
                                            · linarith only [h22672, h22818, hlam]
                                            · rcases p22805_3 (m.d 2 3) (by simp) with h22820 | h22820
                                              · rcases p22805_3 (m.d 2 4) (by simp) with h22821 | h22821
                                                · linarith only [h22681, h22821, hlam]
                                                · linarith only [h19744, h22821, hlam]
                                              · linarith only [h22820, hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          rcases p22805_3 (m.d 0 2) (by simp) with h22825 | h22825
                                          · linarith only [h22825, h4, hlam]
                                          · linarith only [h0, h22825, hlam]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22011, h22681, h4, hc02, hc23, hlam, hphi, p22805_1]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h0, h22011, h22676, h22681, h4, hlam, p22805_2]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          rcases p22805_3 (m.d 0 2) (by simp) with h22831 | h22831
                                          · linarith only [h22831, hlam, p22805_0]
                                          · rcases p22805_3 (m.d 1 2) (by simp) with h22833 | h22833
                                            · linarith only [h22674, h22833, hlam]
                                            · rcases p22805_3 (m.d 2 3) (by simp) with h22835 | h22835
                                              · rcases p22805_3 (m.d 2 4) (by simp) with h22836 | h22836
                                                · rcases p22805_3 (m.d 2 5) (by simp) with h22837 | h22837
                                                  · linarith only [h22683, h22837, hlam]
                                                  · rcases h4bigk with h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c | h22839c
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22011, h22672, h22676, h22677, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22839_1]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h19744, hlam, p22839_1]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22011, hlam, p22839_1]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      rcases p22839_3 (m.d 0 4) (by simp) with h22844 | h22844
                                                      · rcases p22839_3 (m.d 1 4) (by simp) with h22845 | h22845
                                                        · linarith only [h2, h22845, hlam]
                                                        · linarith only [h22680, h22845, hlam]
                                                      · linarith only [h22844, hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h2, hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22674, hlam, p22839_1]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22677, hlam, p22839_1]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p22685_1, p22839_1]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      rcases p22839_3 (m.d 0 4) (by simp) with h22854 | h22854
                                                      · linarith only [h19744, h22854, hlam]
                                                      · rcases p22839_3 (m.d 1 4) (by simp) with h22856 | h22856
                                                        · linarith only [h22674, h22856, hlam]
                                                        · rcases p22839_3 (m.d 2 4) (by simp) with h22858 | h22858
                                                          · rcases p22839_3 (m.d 3 4) (by simp) with h22859 | h22859
                                                            · linarith only [h22681, h22859, hlam]
                                                            · linarith only [h22011, h22859, hlam]
                                                          · linarith only [h19744, h22858, hlam]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      rcases p22839_3 (m.d 0 4) (by simp) with h22863 | h22863
                                                      · linarith only [h19744, h22863, hlam]
                                                      · linarith only [h2, h22863, hlam]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h0, h22011, h22676, h22682, h22684, h4, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22839_1]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h0, h22676, h22682, h22684, hlam, p22805_1, p22839_2]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h0, h22011, h22676, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22839_1]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22674, h22676, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22839_1]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22681, hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      rcases p22839_3 (m.d 0 4) (by simp) with h22873 | h22873
                                                      · linarith only [h22011, h22873, hlam]
                                                      · linarith only [h22671, h22873, hlam]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22671, hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22680, hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22683, hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [h22684, hlam, p22839_0]
                                                    · have p22839_0 := h22839c.1
                                                      have p22839_1 := h22839c.2.1
                                                      have p22839_2 := h22839c.2.2.1
                                                      have p22839_3 := h22839c.2.2.2
                                                      linarith only [hlam, p22839_0]
                                                · linarith only [h22836, hlam, p22805_0]
                                              · linarith only [h22835, h4, hlam]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          rcases p22805_3 (m.d 0 2) (by simp) with h22883 | h22883
                                          · linarith only [h19744, h22883, hlam]
                                          · linarith only [h0, h22883, hlam]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22681, hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          rcases p22805_3 (m.d 0 2) (by simp) with h22888 | h22888
                                          · linarith only [h19744, h22888, hlam]
                                          · linarith only [h22010, h22888, hlam]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22010, hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22676, hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22682, hlam, p22805_0]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [h22683, hlam, p22805_1]
                                        · have p22805_0 := h22805c.1
                                          have p22805_1 := h22805c.2.1
                                          have p22805_2 := h22805c.2.2.1
                                          have p22805_3 := h22805c.2.2.2
                                          linarith only [hlam, p22805_0]
                                      · rcases h2bigk with h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c | h22896c
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22676, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22896_1]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h4, hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h19744, hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22011, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22896_1]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h0, hlam, p22896_1]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22672, hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22674, hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h0, h22011, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22896_1]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          rcases p22896_3 (m.d 0 2) (by simp) with h22907 | h22907
                                          · linarith only [h22907, hlam, p22896_0]
                                          · rcases p22896_3 (m.d 1 2) (by simp) with h22909 | h22909
                                            · linarith only [h22672, h22909, hlam]
                                            · rcases p22896_3 (m.d 2 3) (by simp) with h22911 | h22911
                                              · rcases p22896_3 (m.d 2 4) (by simp) with h22912 | h22912
                                                · linarith only [h22681, h22912, hlam]
                                                · linarith only [h19744, h22912, hlam]
                                              · linarith only [h22911, hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          rcases p22896_3 (m.d 0 2) (by simp) with h22916 | h22916
                                          · linarith only [h22916, h4, hlam]
                                          · linarith only [h0, h22916, hlam]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22011, h22681, h4, hc02, hc23, hlam, hphi, p22896_1]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h0, h22011, h22676, h22681, h4, hlam, p22896_2]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          rcases p22896_3 (m.d 0 2) (by simp) with h22922 | h22922
                                          · linarith only [h22922, hlam, p22896_0]
                                          · rcases p22896_3 (m.d 1 2) (by simp) with h22924 | h22924
                                            · linarith only [h22674, h22924, hlam]
                                            · rcases p22896_3 (m.d 2 3) (by simp) with h22926 | h22926
                                              · rcases p22896_3 (m.d 2 4) (by simp) with h22927 | h22927
                                                · rcases p22896_3 (m.d 2 5) (by simp) with h22928 | h22928
                                                  · linarith only [h22683, h22928, hlam]
                                                  · rcases h4bigk with h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c | h22930c
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22011, h22672, h22676, h22677, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22930_1]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h19744, hlam, p22930_1]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22011, hlam, p22930_1]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      rcases p22930_3 (m.d 0 4) (by simp) with h22935 | h22935
                                                      · rcases p22930_3 (m.d 1 4) (by simp) with h22936 | h22936
                                                        · linarith only [h2, h22936, hlam]
                                                        · linarith only [h22680, h22936, hlam]
                                                      · linarith only [h22935, hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h2, hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22674, hlam, p22930_1]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22677, hlam, p22930_1]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p22685_1, p22930_1]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      rcases p22930_3 (m.d 0 4) (by simp) with h22945 | h22945
                                                      · linarith only [h19744, h22945, hlam]
                                                      · rcases p22930_3 (m.d 1 4) (by simp) with h22947 | h22947
                                                        · linarith only [h22674, h22947, hlam]
                                                        · rcases p22930_3 (m.d 2 4) (by simp) with h22949 | h22949
                                                          · rcases p22930_3 (m.d 3 4) (by simp) with h22950 | h22950
                                                            · linarith only [h22681, h22950, hlam]
                                                            · linarith only [h22011, h22950, hlam]
                                                          · linarith only [h19744, h22949, hlam]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      rcases p22930_3 (m.d 0 4) (by simp) with h22954 | h22954
                                                      · linarith only [h19744, h22954, hlam]
                                                      · linarith only [h2, h22954, hlam]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h0, h22011, h22676, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22930_1]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h0, h22676, h22682, h22684, hlam, p22896_1, p22930_2]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h0, h22011, h22676, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22930_1]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22674, h22676, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22930_1]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22681, hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      rcases p22930_3 (m.d 0 4) (by simp) with h22964 | h22964
                                                      · linarith only [h22011, h22964, hlam]
                                                      · linarith only [h22671, h22964, hlam]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22671, hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22680, hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22683, hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [h22684, hlam, p22930_0]
                                                    · have p22930_0 := h22930c.1
                                                      have p22930_1 := h22930c.2.1
                                                      have p22930_2 := h22930c.2.2.1
                                                      have p22930_3 := h22930c.2.2.2
                                                      linarith only [hlam, p22930_0]
                                                · linarith only [h22927, hlam, p22896_0]
                                              · linarith only [h22926, h4, hlam]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          rcases p22896_3 (m.d 0 2) (by simp) with h22974 | h22974
                                          · linarith only [h19744, h22974, hlam]
                                          · linarith only [h0, h22974, hlam]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22681, hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          rcases p22896_3 (m.d 0 2) (by simp) with h22979 | h22979
                                          · linarith only [h19744, h22979, hlam]
                                          · linarith only [h22010, h22979, hlam]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22010, hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22676, hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22682, hlam, p22896_0]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [h22683, hlam, p22896_1]
                                        · have p22896_0 := h22896c.1
                                          have p22896_1 := h22896c.2.1
                                          have p22896_2 := h22896c.2.2.1
                                          have p22896_3 := h22896c.2.2.2
                                          linarith only [hlam, p22896_0]
                                      · rcases h2bigk with h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c | h22987c
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22676, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22987_1]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h4, hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h19744, hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22011, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22987_1]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h0, hlam, p22987_1]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22672, hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22674, hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h0, h22011, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22987_1]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          rcases p22987_3 (m.d 0 2) (by simp) with h22998 | h22998
                                          · linarith only [h22998, hlam, p22987_0]
                                          · rcases p22987_3 (m.d 1 2) (by simp) with h23000 | h23000
                                            · linarith only [h22672, h23000, hlam]
                                            · rcases p22987_3 (m.d 2 3) (by simp) with h23002 | h23002
                                              · rcases p22987_3 (m.d 2 4) (by simp) with h23003 | h23003
                                                · linarith only [h22681, h23003, hlam]
                                                · linarith only [h19744, h23003, hlam]
                                              · linarith only [h23002, hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          rcases p22987_3 (m.d 0 2) (by simp) with h23007 | h23007
                                          · linarith only [h23007, h4, hlam]
                                          · linarith only [h0, h23007, hlam]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22011, h22681, h4, hc02, hc23, hlam, hphi, p22987_1]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h0, h22011, h22676, h22681, h4, hlam, p22987_2]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          rcases p22987_3 (m.d 0 2) (by simp) with h23013 | h23013
                                          · linarith only [h23013, hlam, p22987_0]
                                          · rcases p22987_3 (m.d 1 2) (by simp) with h23015 | h23015
                                            · linarith only [h22674, h23015, hlam]
                                            · rcases p22987_3 (m.d 2 3) (by simp) with h23017 | h23017
                                              · rcases p22987_3 (m.d 2 4) (by simp) with h23018 | h23018
                                                · rcases p22987_3 (m.d 2 5) (by simp) with h23019 | h23019
                                                  · linarith only [h22683, h23019, hlam]
                                                  · rcases h4bigk with h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c | h23021c
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22011, h22672, h22676, h22677, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23021_1]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h19744, hlam, p23021_1]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22011, hlam, p23021_1]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      rcases p23021_3 (m.d 0 4) (by simp) with h23026 | h23026
                                                      · rcases p23021_3 (m.d 1 4) (by simp) with h23027 | h23027
                                                        · linarith only [h2, h23027, hlam]
                                                        · linarith only [h22680, h23027, hlam]
                                                      · linarith only [h23026, hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h2, hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22674, hlam, p23021_1]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22677, hlam, p23021_1]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p22685_1, p23021_1]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      rcases p23021_3 (m.d 0 4) (by simp) with h23036 | h23036
                                                      · linarith only [h19744, h23036, hlam]
                                                      · rcases p23021_3 (m.d 1 4) (by simp) with h23038 | h23038
                                                        · linarith only [h22674, h23038, hlam]
                                                        · rcases p23021_3 (m.d 2 4) (by simp) with h23040 | h23040
                                                          · rcases p23021_3 (m.d 3 4) (by simp) with h23041 | h23041
                                                            · linarith only [h22681, h23041, hlam]
                                                            · linarith only [h22011, h23041, hlam]
                                                          · linarith only [h19744, h23040, hlam]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      rcases p23021_3 (m.d 0 4) (by simp) with h23045 | h23045
                                                      · linarith only [h19744, h23045, hlam]
                                                      · linarith only [h2, h23045, hlam]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h0, h22011, h22676, h22682, h22684, h4, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23021_1]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h0, h22676, h22682, h22684, hlam, p22987_1, p23021_2]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h0, h22011, h22676, h22681, h22682, h22684, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23021_1]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22674, h22676, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23021_1]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22681, hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      rcases p23021_3 (m.d 0 4) (by simp) with h23055 | h23055
                                                      · linarith only [h22011, h23055, hlam]
                                                      · linarith only [h22671, h23055, hlam]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22671, hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22680, hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22683, hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [h22684, hlam, p23021_0]
                                                    · have p23021_0 := h23021c.1
                                                      have p23021_1 := h23021c.2.1
                                                      have p23021_2 := h23021c.2.2.1
                                                      have p23021_3 := h23021c.2.2.2
                                                      linarith only [hlam, p23021_0]
                                                · linarith only [h23018, hlam, p22987_0]
                                              · linarith only [h23017, h4, hlam]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          rcases p22987_3 (m.d 0 2) (by simp) with h23065 | h23065
                                          · linarith only [h19744, h23065, hlam]
                                          · linarith only [h0, h23065, hlam]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22681, hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          rcases p22987_3 (m.d 0 2) (by simp) with h23070 | h23070
                                          · linarith only [h19744, h23070, hlam]
                                          · linarith only [h22010, h23070, hlam]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22010, hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22676, hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22682, hlam, p22987_0]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [h22683, hlam, p22987_1]
                                        · have p22987_0 := h22987c.1
                                          have p22987_1 := h22987c.2.1
                                          have p22987_2 := h22987c.2.2.1
                                          have p22987_3 := h22987c.2.2.2
                                          linarith only [hlam, p22987_0]
                            · linarith only [h22703, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            rcases p22685_3 (m.d 0 1) (by simp) with h23079 | h23079
                            · rcases p22685_3 (m.d 1 2) (by simp) with h23080 | h23080
                              · linarith only [h0, h23080, hlam]
                              · linarith only [h22676, h23080, hlam]
                            · linarith only [h23079, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h0, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h22672, hlam, p22685_1]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h22674, hlam, p22685_1]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h0, h22011, h22681, h4, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p22685_1]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h1, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h1, h22676, hc01, hc25, hlam, hphi, ht0b, ht5b, p22685_1]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h22677, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h1, h22011, h22676, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22685_1]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h2, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h2, h22676, h22682, h22684, hc01, hc45, hlam, hphi, ht0b, ht5b, p22685_1]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h2, h22011, h22672, h22676, h22681, h22682, h22684, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22685_1]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            rcases p22685_3 (m.d 0 1) (by simp) with h23098 | h23098
                            · rcases p22685_3 (m.d 1 2) (by simp) with h23099 | h23099
                              · linarith only [h22674, h23099, hlam]
                              · linarith only [h22676, h23099, hlam]
                            · linarith only [h23098, h3, hlam]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h3, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h22676, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h22679, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [h22680, hlam, p22685_0]
                          · have p22685_0 := h22685c.1
                            have p22685_1 := h22685c.2.1
                            have p22685_2 := h22685c.2.2.1
                            have p22685_3 := h22685c.2.2.2
                            linarith only [hlam, p22685_0]
                        · linarith only [h22011, h22671, h22684, hlam]
                      · linarith only [h0, h19744, h22676, h22680, h22683, h3, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h22011, h22681, h22682, h4, hc02, hc35, hlam, hphi, ht23]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h23111 | h23111
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h23112 | h23112
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h23113 | h23113
                        · rcases h1bigk with h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c | h23114c
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            rcases p23114_3 (m.d 0 1) (by simp) with h23116 | h23116
                            · rcases p23114_3 (m.d 1 2) (by simp) with h23117 | h23117
                              · linarith only [h23117, hlam, p23114_0]
                              · rcases p23114_3 (m.d 1 3) (by simp) with h23119 | h23119
                                · linarith only [h1, h23119, hlam]
                                · linarith only [h22672, h23119, hlam]
                            · linarith only [h23116, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            rcases p23114_3 (m.d 0 1) (by simp) with h23123 | h23123
                            · rcases p23114_3 (m.d 1 2) (by simp) with h23124 | h23124
                              · linarith only [h0, h23124, hlam]
                              · rcases p23114_3 (m.d 1 3) (by simp) with h23126 | h23126
                                · linarith only [h23126, hlam, p23114_0]
                                · rcases p23114_3 (m.d 1 4) (by simp) with h23128 | h23128
                                  · linarith only [h2, h23128, hlam]
                                  · linarith only [h22677, h23128, hlam]
                            · linarith only [h23123, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            rcases p23114_3 (m.d 0 1) (by simp) with h23132 | h23132
                            · rcases p23114_3 (m.d 1 2) (by simp) with h23133 | h23133
                              · linarith only [h0, h23133, hlam]
                              · rcases p23114_3 (m.d 1 3) (by simp) with h23135 | h23135
                                · linarith only [h1, h23135, hlam]
                                · rcases p23114_3 (m.d 1 4) (by simp) with h23137 | h23137
                                  · linarith only [h23137, hlam, p23114_0]
                                  · rcases p23114_3 (m.d 1 5) (by simp) with h23139 | h23139
                                    · linarith only [h23139, h3, hlam]
                                    · rcases h1emax with h23141 | h23141 | h23141 | h23141 | h23141
                                      · linarith only [h22677, h23141, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p23114_1]
                                      · rcases h2bigk with h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c | h23143c
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22676, h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23143_1]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h4, hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h19744, hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23143_1]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h0, hlam, p23143_1]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22672, hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22674, hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22672, h22677, h23111, h23113, hc01, hc45, hlam, hphi, ht0b, ht5b, p23114_1, p23143_1]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22681, hc02, hc34, hlam, hphi, ht23, p23143_1]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22681, hc12, hc34, hlam, hphi, ht23, p23143_1]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22681, hlam, p23143_1]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          rcases p23143_3 (m.d 0 2) (by simp) with h23158 | h23158
                                          · linarith only [h23158, h4, hlam]
                                          · linarith only [h22010, h23158, hlam]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          rcases p23143_3 (m.d 0 2) (by simp) with h23161 | h23161
                                          · linarith only [h23161, hlam, p23143_0]
                                          · rcases p23143_3 (m.d 1 2) (by simp) with h23163 | h23163
                                            · linarith only [h22674, h23163, hlam]
                                            · rcases p23143_3 (m.d 2 3) (by simp) with h23165 | h23165
                                              · linarith only [h22681, h23165, hlam]
                                              · linarith only [h23165, h4, hlam]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          rcases p23143_3 (m.d 0 2) (by simp) with h23168 | h23168
                                          · linarith only [h19744, h23168, hlam]
                                          · linarith only [h0, h23168, hlam]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h0, h22676, h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23143_1]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          rcases p23143_3 (m.d 0 2) (by simp) with h23173 | h23173
                                          · linarith only [h19744, h23173, hlam]
                                          · linarith only [h22010, h23173, hlam]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22010, hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h22676, hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h23111, hlam, p23143_0]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [h23112, hlam, p23143_1]
                                        · have p23143_0 := h23143c.1
                                          have p23143_1 := h23143c.2.1
                                          have p23143_2 := h23143c.2.2.1
                                          have p23143_3 := h23143c.2.2.2
                                          linarith only [hlam, p23143_0]
                                      · rcases h2bigk with h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c | h23181c
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h22676, h23111, h23113, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23181_1]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h4, hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h19744, hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23181_1]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h0, hlam, p23181_1]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h22672, hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h22674, hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h0, h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23181_1]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h22681, hc02, hc34, hlam, hphi, ht23, p23181_1]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h22681, hc12, hc34, hlam, hphi, ht23, p23181_1]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h22681, hlam, p23181_1]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          rcases p23181_3 (m.d 0 2) (by simp) with h23196 | h23196
                                          · linarith only [h23196, h4, hlam]
                                          · linarith only [h22010, h23196, hlam]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          rcases p23181_3 (m.d 0 2) (by simp) with h23199 | h23199
                                          · linarith only [h23199, hlam, p23181_0]
                                          · rcases p23181_3 (m.d 1 2) (by simp) with h23201 | h23201
                                            · linarith only [h22674, h23201, hlam]
                                            · rcases p23181_3 (m.d 2 3) (by simp) with h23203 | h23203
                                              · linarith only [h22681, h23203, hlam]
                                              · linarith only [h23203, h4, hlam]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          rcases p23181_3 (m.d 0 2) (by simp) with h23206 | h23206
                                          · linarith only [h19744, h23206, hlam]
                                          · linarith only [h0, h23206, hlam]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h0, h22676, h23111, h23113, h4, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23181_1]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          rcases p23181_3 (m.d 0 2) (by simp) with h23211 | h23211
                                          · linarith only [h19744, h23211, hlam]
                                          · linarith only [h22010, h23211, hlam]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h22010, hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h22676, hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h23111, hlam, p23181_0]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [h23112, hlam, p23181_1]
                                        · have p23181_0 := h23181c.1
                                          have p23181_1 := h23181c.2.1
                                          have p23181_2 := h23181c.2.2.1
                                          have p23181_3 := h23181c.2.2.2
                                          linarith only [hlam, p23181_0]
                                      · rcases h2bigk with h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c | h23219c
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22676, h23111, h23113, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23219_1]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h4, hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h19744, hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23219_1]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h0, hlam, p23219_1]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22672, hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22674, hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h0, h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23219_1]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22681, hc02, hc34, hlam, hphi, ht23, p23219_1]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22681, hc12, hc34, hlam, hphi, ht23, p23219_1]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22681, hlam, p23219_1]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          rcases p23219_3 (m.d 0 2) (by simp) with h23234 | h23234
                                          · linarith only [h23234, h4, hlam]
                                          · linarith only [h22010, h23234, hlam]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          rcases p23219_3 (m.d 0 2) (by simp) with h23237 | h23237
                                          · linarith only [h23237, hlam, p23219_0]
                                          · rcases p23219_3 (m.d 1 2) (by simp) with h23239 | h23239
                                            · linarith only [h22674, h23239, hlam]
                                            · rcases p23219_3 (m.d 2 3) (by simp) with h23241 | h23241
                                              · linarith only [h22681, h23241, hlam]
                                              · linarith only [h23241, h4, hlam]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          rcases p23219_3 (m.d 0 2) (by simp) with h23244 | h23244
                                          · linarith only [h19744, h23244, hlam]
                                          · linarith only [h0, h23244, hlam]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22681, h4, hc02, hc34, hlam, hphi, ht23, p23219_1]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          rcases p23219_3 (m.d 0 2) (by simp) with h23249 | h23249
                                          · linarith only [h19744, h23249, hlam]
                                          · linarith only [h22010, h23249, hlam]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22010, hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h22676, hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h23111, hlam, p23219_0]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [h23112, hlam, p23219_1]
                                        · have p23219_0 := h23219c.1
                                          have p23219_1 := h23219c.2.1
                                          have p23219_2 := h23219c.2.2.1
                                          have p23219_3 := h23219c.2.2.2
                                          linarith only [hlam, p23219_0]
                                      · rcases h2bigk with h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c | h23257c
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22676, h23111, h23113, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23257_1]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h4, hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h19744, hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23257_1]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h0, hlam, p23257_1]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22672, hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22674, hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h0, h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23257_1]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22681, hc02, hc34, hlam, hphi, ht23, p23257_1]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22681, hc12, hc34, hlam, hphi, ht23, p23257_1]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22681, hlam, p23257_1]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          rcases p23257_3 (m.d 0 2) (by simp) with h23272 | h23272
                                          · linarith only [h23272, h4, hlam]
                                          · linarith only [h22010, h23272, hlam]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          rcases p23257_3 (m.d 0 2) (by simp) with h23275 | h23275
                                          · linarith only [h23275, hlam, p23257_0]
                                          · rcases p23257_3 (m.d 1 2) (by simp) with h23277 | h23277
                                            · linarith only [h22674, h23277, hlam]
                                            · rcases p23257_3 (m.d 2 3) (by simp) with h23279 | h23279
                                              · linarith only [h22681, h23279, hlam]
                                              · linarith only [h23279, h4, hlam]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          rcases p23257_3 (m.d 0 2) (by simp) with h23282 | h23282
                                          · linarith only [h19744, h23282, hlam]
                                          · linarith only [h0, h23282, hlam]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22681, h4, hc02, hc34, hlam, hphi, ht23, p23257_1]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          rcases p23257_3 (m.d 0 2) (by simp) with h23287 | h23287
                                          · linarith only [h19744, h23287, hlam]
                                          · linarith only [h22010, h23287, hlam]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22010, hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h22676, hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h23111, hlam, p23257_0]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [h23112, hlam, p23257_1]
                                        · have p23257_0 := h23257c.1
                                          have p23257_1 := h23257c.2.1
                                          have p23257_2 := h23257c.2.2.1
                                          have p23257_3 := h23257c.2.2.2
                                          linarith only [hlam, p23257_0]
                            · linarith only [h23132, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            rcases p23114_3 (m.d 0 1) (by simp) with h23296 | h23296
                            · rcases p23114_3 (m.d 1 2) (by simp) with h23297 | h23297
                              · linarith only [h0, h23297, hlam]
                              · linarith only [h22676, h23297, hlam]
                            · linarith only [h23296, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h0, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h22672, hlam, p23114_1]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h22674, hlam, p23114_1]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h0, h22676, h22681, h23111, h23113, h4, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p23114_1]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h1, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h1, h22011, hc12, hc34, hlam, hphi, ht23, p23114_1]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h22677, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            rcases p23114_3 (m.d 0 1) (by simp) with h23310 | h23310
                            · rcases p23114_3 (m.d 1 2) (by simp) with h23311 | h23311
                              · linarith only [h22672, h23311, hlam]
                              · linarith only [h22676, h23311, hlam]
                            · linarith only [h23310, h3, hlam]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h2, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h2, h22676, h23111, h23113, hc01, hc45, hlam, hphi, ht0b, ht5b, p23114_1]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h2, h22672, h22676, h23111, h23113, hc01, hc45, hlam, hphi, ht0b, ht5b, p23114_1]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            rcases p23114_3 (m.d 0 1) (by simp) with h23319 | h23319
                            · rcases p23114_3 (m.d 1 2) (by simp) with h23320 | h23320
                              · linarith only [h22674, h23320, hlam]
                              · linarith only [h22676, h23320, hlam]
                            · linarith only [h23319, h3, hlam]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h3, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h22676, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h22679, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [h22680, hlam, p23114_0]
                          · have p23114_0 := h23114c.1
                            have p23114_1 := h23114c.2.1
                            have p23114_2 := h23114c.2.2.1
                            have p23114_3 := h23114c.2.2.2
                            linarith only [hlam, p23114_0]
                        · linarith only [h22681, h23113, h4, hc02, hc45, hlam, hphi, ht23, ht34]
                      · linarith only [h19744, h22010, h22011, h22680, h22681, h23112, h3, h4, hc03, hc34, hlam, hphi]
                    · linarith only [h0, h22011, h22670, h22676, h23111, h4, hc04, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h22672, h22676, h22677, h22680, hlam]
              · linarith only [h22011, h22670, h22672, h22676, h22679, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · linarith only [h22010, h22676, h4, hc12, hc23, hlam, hphi]
    · linarith only [h22010, h22011, h22671, h4, hlam]
  · linarith only [h22010, h22670, h4, hlam]

set_option maxHeartbeats 19774000 in
set_option maxHeartbeats 19774000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h22010 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  rcases m.htr 0 3 4 (by decide) (by decide) with h22011 | h22011
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 h22010 h22011
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 h22010 h22011

set_option maxHeartbeats 19774000 in
set_option maxHeartbeats 19774000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s23 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h19744 h22010

set_option maxHeartbeats 19774000 in
set_option maxHeartbeats 19774000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  rcases m.htr 0 2 5 (by decide) (by decide) with h22010 | h22010
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 h22010
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 h22010

end R2N4
