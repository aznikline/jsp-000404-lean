import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S35
import Jsp000404.R1LeavesN7_3S36

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13248000 in
set_option maxHeartbeats 13248000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s15_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h17994 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h17995 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  rcases m.htr 0 2 4 (by decide) (by decide) with h18721 | h18721
  · rcases m.htr 0 2 5 (by decide) (by decide) with h18722 | h18722
    · rcases m.htr 0 3 4 (by decide) (by decide) with h18723 | h18723
      · rcases m.htr 0 3 5 (by decide) (by decide) with h18724 | h18724
        · rcases m.htr 0 4 5 (by decide) (by decide) with h18725 | h18725
          · rcases m.htr 1 2 3 (by decide) (by decide) with h18726 | h18726
            · rcases m.htr 1 2 4 (by decide) (by decide) with h18727 | h18727
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18728 | h18728
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18729 | h18729
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18730 | h18730
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18731 | h18731
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18732 | h18732
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18733 | h18733
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18734 | h18734
                            · linarith only [h17995, h18721, h18726, h18734, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h17995, h18721, h18725, h18726, h18734, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h16563, h17994, h17995, h18721, h18724, h18733, hc03, hc15, hlam, hphi, ht0b, ht5b]
                        · linarith only [h16563, h17994, h17995, h18721, h18723, h18732, hc03, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h16563, h17994, h18721, h18725, h18728, h18731, hc02, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h14799, h18724, h18730, hlam]
                  · linarith only [h14799, h17994, h17995, h18721, h18723, h18726, h18728, h18729, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                · linarith only [h17995, h18726, h18728, hc02, hc25, hlam, hphi]
              · linarith only [h17995, h18726, h18727, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h18744 | h18744
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18745 | h18745
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18746 | h18746
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18747 | h18747
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18748 | h18748
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18749 | h18749
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18750 | h18750
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18751 | h18751
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18752 | h18752
                              · rcases h1bigk with h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c | h18753c
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h0, hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h14799, hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h16563, hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h16563, h18726, h18744, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p18753_1]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h18726, hc01, hc23, hlam, hphi, ht12, p18753_1]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h18726, hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h16563, h18726, hc01, hc23, hlam, hphi, ht12, p18753_1]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  rcases p18753_3 (m.d 0 1) (by simp) with h18763 | h18763
                                  · linarith only [h0, h18763, hlam]
                                  · linarith only [h17994, h18763, hlam]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  rcases p18753_3 (m.d 0 1) (by simp) with h18766 | h18766
                                  · linarith only [h18766, hlam, p18753_0]
                                  · rcases p18753_3 (m.d 1 2) (by simp) with h18768 | h18768
                                    · linarith only [h18726, h18768, hlam]
                                    · linarith only [h0, h18768, hlam]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h0, h17994, h18726, h18745, h18750, h18752, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18753_1]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h16563, h17994, h18726, h18745, h18750, h18752, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18753_1]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  rcases p18753_3 (m.d 0 1) (by simp) with h18774 | h18774
                                  · linarith only [h14799, h18774, hlam]
                                  · linarith only [h17994, h18774, hlam]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h17994, h18726, h18744, h18745, h18750, h18752, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18753_1]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h18744, hlam, p18753_1]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h18746, hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  rcases p18753_3 (m.d 0 1) (by simp) with h18781 | h18781
                                  · linarith only [h16563, h18781, hlam]
                                  · linarith only [h17994, h18781, hlam]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h17994, hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h18745, hlam, p18753_1]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h18747, hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [h18748, hlam, p18753_0]
                                · have p18753_0 := h18753c.1
                                  have p18753_1 := h18753c.2.1
                                  have p18753_2 := h18753c.2.2.1
                                  have p18753_3 := h18753c.2.2.2
                                  linarith only [hlam, p18753_0]
                              · linarith only [h0, h17994, h18726, h18748, h18752, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h16563, h17994, h18726, h18744, h18748, h18751, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h16563, h18726, h18744, h18750, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h16563, h17994, h18726, h18744, h18748, h18749, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h16563, h18725, h18748, hlam]
                    · linarith only [h14799, h18724, h18747, hlam]
                  · linarith only [h14799, h18723, h18746, hlam]
                · linarith only [h14799, h16563, h17995, h18722, h18744, h18745, hc01, hc13, hlam, hphi]
              · linarith only [h0, h18721, h18744, hlam]
          · linarith only [h16563, h17994, h18725, hlam]
        · linarith only [h0, h17994, h17995, h18724, hlam]
      · linarith only [h17995, h18721, h18723, hlam]
    · linarith only [h16563, h17994, h18721, h18722, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h18802 | h18802
    · rcases m.htr 0 3 4 (by decide) (by decide) with h18803 | h18803
      · rcases m.htr 0 3 5 (by decide) (by decide) with h18804 | h18804
        · rcases m.htr 0 4 5 (by decide) (by decide) with h18805 | h18805
          · rcases m.htr 1 2 3 (by decide) (by decide) with h18806 | h18806
            · rcases m.htr 1 2 4 (by decide) (by decide) with h18807 | h18807
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18808 | h18808
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18809 | h18809
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18810 | h18810
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18811 | h18811
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18812 | h18812
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18813 | h18813
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18814 | h18814
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18815 | h18815
                              · rcases h1bigk with h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c | h18816c
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h0, hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h14799, hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h16563, hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h0, h17995, h18806, h18808, h18813, h18815, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18816_1]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  rcases p18816_3 (m.d 0 1) (by simp) with h18822 | h18822
                                  · linarith only [h18822, hlam, p18816_0]
                                  · rcases p18816_3 (m.d 1 2) (by simp) with h18824 | h18824
                                    · rcases p18816_3 (m.d 1 3) (by simp) with h18825 | h18825
                                      · linarith only [h18806, h18825, hlam]
                                      · linarith only [h14799, h18825, hlam]
                                    · linarith only [h18824, hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h0, h18721, h18807, h18809, hc01, hc12, hlam, hphi, p18816_1]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h0, h17994, h18721, h18807, h18808, h18813, h18815, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18816_1]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h0, h17994, h17995, h18806, hlam, p18816_2]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  rcases p18816_3 (m.d 0 1) (by simp) with h18833 | h18833
                                  · linarith only [h18833, hlam, p18816_0]
                                  · rcases p18816_3 (m.d 1 2) (by simp) with h18835 | h18835
                                    · rcases p18816_3 (m.d 1 3) (by simp) with h18836 | h18836
                                      · rcases p18816_3 (m.d 1 4) (by simp) with h18837 | h18837
                                        · linarith only [h18809, h18837, hlam]
                                        · linarith only [h16563, h18837, hlam]
                                      · linarith only [h18836, hlam, p18816_0]
                                    · linarith only [h0, h18835, hlam]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h18806, hlam, p18816_1]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h0, h17994, h18721, h18807, h18808, h18813, h18815, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p18816_1]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  rcases p18816_3 (m.d 0 1) (by simp) with h18845 | h18845
                                  · linarith only [h14799, h18845, hlam]
                                  · linarith only [h17994, h18845, hlam]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  rcases p18816_3 (m.d 0 1) (by simp) with h18848 | h18848
                                  · linarith only [h18848, hlam, p18816_0]
                                  · rcases p18816_3 (m.d 1 2) (by simp) with h18850 | h18850
                                    · rcases p18816_3 (m.d 1 3) (by simp) with h18851 | h18851
                                      · rcases p18816_3 (m.d 1 4) (by simp) with h18852 | h18852
                                        · rcases p18816_3 (m.d 1 5) (by simp) with h18853 | h18853
                                          · linarith only [h18811, h18853, hlam]
                                          · rcases h3bigk with h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c | h18855c
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h14799, hlam, p18855_1]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h17995, hlam, p18855_1]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h17995, h18806, h18815, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18855_1]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              rcases p18855_3 (m.d 0 3) (by simp) with h18860 | h18860
                                              · rcases p18855_3 (m.d 1 3) (by simp) with h18861 | h18861
                                                · rcases p18855_3 (m.d 2 3) (by simp) with h18862 | h18862
                                                  · rcases p18855_3 (m.d 3 4) (by simp) with h18863 | h18863
                                                    · linarith only [h18803, h18863, hlam]
                                                    · linarith only [h18815, h18863, hlam]
                                                  · linarith only [h18813, h18862, hlam]
                                                · linarith only [h18810, h18861, hlam]
                                              · linarith only [h18860, hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18803, h18815, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p18855_1]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h0, h17994, h17995, h18806, h18808, h18813, h18815, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18855_1]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              rcases p18855_3 (m.d 0 3) (by simp) with h18872 | h18872
                                              · linarith only [h14799, h18872, hlam]
                                              · linarith only [h18803, h18872, hlam]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h17994, h18808, h18809, h18813, hlam, p18816_1, p18855_2]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18803, h18815, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18855_1]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18806, hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18806, h18815, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18855_1]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              rcases p18855_3 (m.d 0 3) (by simp) with h18880 | h18880
                                              · linarith only [h17995, h18880, hlam]
                                              · linarith only [h18804, h18880, hlam]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18803, hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18809, hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18812, hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h17995, h18803, h18806, h18815, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18855_1]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18804, hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18810, hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18813, hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [h18815, hlam, p18855_0]
                                            · have p18855_0 := h18855c.1
                                              have p18855_1 := h18855c.2.1
                                              have p18855_2 := h18855c.2.2.1
                                              have p18855_3 := h18855c.2.2.2
                                              linarith only [hlam, p18855_0]
                                        · linarith only [h18852, hlam, p18816_0]
                                      · linarith only [h14799, h18851, hlam]
                                    · linarith only [h0, h18850, hlam]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h18807, hlam, p18816_1]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h18809, hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  rcases p18816_3 (m.d 0 1) (by simp) with h18899 | h18899
                                  · linarith only [h16563, h18899, hlam]
                                  · linarith only [h17994, h18899, hlam]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h17994, hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h18808, hlam, p18816_1]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h18810, hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [h18811, hlam, p18816_0]
                                · have p18816_0 := h18816c.1
                                  have p18816_1 := h18816c.2.1
                                  have p18816_2 := h18816c.2.2.1
                                  have p18816_3 := h18816c.2.2.2
                                  linarith only [hlam, p18816_0]
                              · linarith only [h0, h17994, h17995, h18806, h18811, h18815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h0, h17994, h18721, h18811, h18814, hlam]
                          · linarith only [h17995, h18804, h18813, hlam]
                        · linarith only [h17995, h18803, h18812, hlam]
                      · linarith only [h16563, h17995, h18803, h18805, h18806, h18811, hc01, hc12, hlam, hphi]
                    · linarith only [h14799, h18804, h18810, hlam]
                  · linarith only [h17995, h18803, h18806, h18809, hlam]
                · linarith only [h0, h17994, h18802, h18808, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h17995, h18806, h18807, hc02, hc24, hlam, hphi]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h18916 | h18916
              · linarith only [h0, h17994, h18721, h18806, h18916, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18918 | h18918
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18919 | h18919
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18920 | h18920
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18921 | h18921
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18922 | h18922
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18923 | h18923
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18924 | h18924
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18925 | h18925
                              · rcases h1bigk with h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c | h18926c
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h0, hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h14799, hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h16563, hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h0, h18916, h18918, h18922, h18923, h18925, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18926_1]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h18916, h18922, hc01, hc23, hlam, hphi, ht12, p18926_1]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h18806, hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h18916, hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  rcases p18926_3 (m.d 0 1) (by simp) with h18936 | h18936
                                  · linarith only [h0, h18936, hlam]
                                  · linarith only [h17994, h18936, hlam]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  rcases p18926_3 (m.d 0 1) (by simp) with h18939 | h18939
                                  · linarith only [h18939, hlam, p18926_0]
                                  · rcases p18926_3 (m.d 1 2) (by simp) with h18941 | h18941
                                    · linarith only [h18806, h18941, hlam]
                                    · linarith only [h0, h18941, hlam]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h0, h17994, h18806, h18918, h18923, h18925, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18926_1]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h0, h17994, h18806, h18916, h18918, h18923, h18925, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p18926_1]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  rcases p18926_3 (m.d 0 1) (by simp) with h18947 | h18947
                                  · linarith only [h14799, h18947, hlam]
                                  · linarith only [h17994, h18947, hlam]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  rcases p18926_3 (m.d 0 1) (by simp) with h18950 | h18950
                                  · linarith only [h18950, hlam, p18926_0]
                                  · rcases p18926_3 (m.d 1 2) (by simp) with h18952 | h18952
                                    · linarith only [h18916, h18952, hlam]
                                    · linarith only [h0, h18952, hlam]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h0, h17994, h18918, h18919, h18923, h18925, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p18926_1]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h18919, hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  rcases p18926_3 (m.d 0 1) (by simp) with h18958 | h18958
                                  · linarith only [h16563, h18958, hlam]
                                  · linarith only [h17994, h18958, hlam]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h17994, hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h18918, hlam, p18926_1]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h18920, hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [h18921, hlam, p18926_0]
                                · have p18926_0 := h18926c.1
                                  have p18926_1 := h18926c.2.1
                                  have p18926_2 := h18926c.2.2.1
                                  have p18926_3 := h18926c.2.2.2
                                  linarith only [hlam, p18926_0]
                              · linarith only [h0, h17994, h18806, h18921, h18925, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h17994, h18916, h18921, h18924, hlam]
                          · linarith only [h0, h18916, h18922, h18923, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h0, h18806, h18922, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h17994, h18805, h18916, h18918, h18921, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h14799, h18804, h18920, hlam]
                  · linarith only [h14799, h18803, h18919, hlam]
                · linarith only [h0, h17994, h18802, h18918, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h17994, h18721, h18805, hlam]
        · linarith only [h0, h17994, h18721, h18803, h18804, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h18976 | h18976
        · rcases m.htr 0 4 5 (by decide) (by decide) with h18977 | h18977
          · rcases m.htr 1 2 3 (by decide) (by decide) with h18978 | h18978
            · rcases m.htr 1 2 4 (by decide) (by decide) with h18979 | h18979
              · rcases m.htr 1 2 5 (by decide) (by decide) with h18980 | h18980
                · rcases m.htr 1 3 4 (by decide) (by decide) with h18981 | h18981
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18982 | h18982
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18983 | h18983
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18984 | h18984
                        · linarith only [h0, h17994, h17995, h18803, h18978, h18980, h18984, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h17994, h17995, h18980, h18981, h18984, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h18721, h18977, h18979, h18983, hlam]
                    · linarith only [h14799, h17994, h18976, h18980, h18982, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h18989 | h18989
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h18990 | h18990
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h18991 | h18991
                        · linarith only [h18978, h18981, h18991, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h18993 | h18993
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h18994 | h18994
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h18995 | h18995
                              · rcases h1bigk with h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c | h18996c
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h0, hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h14799, hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h16563, hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h14799, h18980, h18981, h18993, h18995, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18996_1]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  rcases p18996_3 (m.d 0 1) (by simp) with h19002 | h19002
                                  · linarith only [h19002, hlam, p18996_0]
                                  · rcases p18996_3 (m.d 1 2) (by simp) with h19004 | h19004
                                    · rcases p18996_3 (m.d 1 3) (by simp) with h19005 | h19005
                                      · linarith only [h18978, h19005, hlam]
                                      · linarith only [h14799, h19005, hlam]
                                    · linarith only [h19004, hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h14799, hc01, hc12, hlam, hphi, p18996_1]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h0, h17994, h17995, h18978, h18980, h18981, h18993, h18995, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p18996_1]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h0, h17994, h17995, h18978, hlam, p18996_2]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h17994, h18980, h18981, h18993, h18995, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p18996_1]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h18978, hlam, p18996_1]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h18981, hlam, p18996_1]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  rcases p18996_3 (m.d 0 1) (by simp) with h19017 | h19017
                                  · linarith only [h14799, h19017, hlam]
                                  · linarith only [h17994, h19017, hlam]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  rcases p18996_3 (m.d 0 1) (by simp) with h19020 | h19020
                                  · linarith only [h19020, hlam, p18996_0]
                                  · rcases p18996_3 (m.d 1 2) (by simp) with h19022 | h19022
                                    · rcases p18996_3 (m.d 1 3) (by simp) with h19023 | h19023
                                      · linarith only [h18981, h19023, hlam]
                                      · linarith only [h14799, h19023, hlam]
                                    · linarith only [h0, h19022, hlam]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h18979, hlam, p18996_1]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h14799, h17994, h18980, h18993, h18995, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p18996_1]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  rcases p18996_3 (m.d 0 1) (by simp) with h19030 | h19030
                                  · linarith only [h16563, h19030, hlam]
                                  · linarith only [h17994, h19030, hlam]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h17994, hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h18980, hlam, p18996_1]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h18989, hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [h18990, hlam, p18996_0]
                                · have p18996_0 := h18996c.1
                                  have p18996_1 := h18996c.2.1
                                  have p18996_2 := h18996c.2.2.1
                                  have p18996_3 := h18996c.2.2.2
                                  linarith only [hlam, p18996_0]
                              · linarith only [h0, h17995, h18721, h18803, h18977, h18979, h18995, hc01, hc12, hlam, hphi]
                            · linarith only [h16563, h17994, h18721, h18990, h18994, hlam]
                          · linarith only [h0, h17994, h17995, h18803, h18976, h18993, hc04, hc15, hlam, hphi, ht0b, ht5b]
                      · linarith only [h0, h17994, h17995, h18977, h18978, h18981, h18990, hc04, hc15, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h17994, h17995, h18976, h18978, h18980, h18989, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h18802, h18980, hlam]
              · linarith only [h0, h17994, h17995, h18978, h18979, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19045 | h19045
              · linarith only [h0, h17994, h18721, h18978, h19045, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19047 | h19047
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19048 | h19048
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19049 | h19049
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19050 | h19050
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19051 | h19051
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19052 | h19052
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19053 | h19053
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h19054 | h19054
                              · rcases h1bigk with h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c | h19055c
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h0, hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h14799, hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h16563, hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h0, h19045, h19047, h19051, h19052, h19054, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19055_1]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h19045, h19051, hc01, hc23, hlam, hphi, ht12, p19055_1]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h18978, hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h19045, hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  rcases p19055_3 (m.d 0 1) (by simp) with h19065 | h19065
                                  · linarith only [h0, h19065, hlam]
                                  · linarith only [h17994, h19065, hlam]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  rcases p19055_3 (m.d 0 1) (by simp) with h19068 | h19068
                                  · linarith only [h19068, hlam, p19055_0]
                                  · rcases p19055_3 (m.d 1 2) (by simp) with h19070 | h19070
                                    · linarith only [h18978, h19070, hlam]
                                    · linarith only [h0, h19070, hlam]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h0, h17994, h18978, h19047, h19052, h19054, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19055_1]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h0, h17994, h18978, h19045, h19047, h19052, h19054, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p19055_1]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h0, h17994, h17995, h18803, h19048, hlam, p19055_2]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  rcases p19055_3 (m.d 0 1) (by simp) with h19077 | h19077
                                  · linarith only [h19077, hlam, p19055_0]
                                  · rcases p19055_3 (m.d 1 2) (by simp) with h19079 | h19079
                                    · linarith only [h19045, h19079, hlam]
                                    · linarith only [h0, h19079, hlam]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h0, h17994, h19047, h19052, h19054, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p19055_1]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h19048, hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  rcases p19055_3 (m.d 0 1) (by simp) with h19085 | h19085
                                  · linarith only [h16563, h19085, hlam]
                                  · linarith only [h17994, h19085, hlam]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h17994, hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h19047, hlam, p19055_1]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h19049, hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [h19050, hlam, p19055_0]
                                · have p19055_0 := h19055c.1
                                  have p19055_1 := h19055c.2.1
                                  have p19055_2 := h19055c.2.2.1
                                  have p19055_3 := h19055c.2.2.2
                                  linarith only [hlam, p19055_0]
                              · linarith only [h0, h17994, h17995, h18803, h18977, h19047, h19052, h19054, hc04, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h17994, h17995, h18803, h19048, h19050, h19053, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · linarith only [h0, h17995, h18803, h18978, h19048, h19052, hc01, hc35, hlam, hphi, ht12, ht23]
                        · linarith only [h18978, h19048, h19051, hlam]
                      · linarith only [h16563, h17994, h18977, h19047, h19050, hc04, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h17994, h17995, h18803, h19047, h19048, h19049, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19099 | h19099
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19100 | h19100
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19101 | h19101
                        · linarith only [h0, h17994, h18978, h19047, h19048, h19101, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h17994, h18978, h19047, h19101, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                      · linarith only [h16563, h18977, h19100, hlam]
                    · linarith only [h0, h17994, h18976, h18978, h19047, h19099, hc03, hc25, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h18802, h19047, hlam]
          · linarith only [h14799, h17994, h18803, h18977, hlam]
        · linarith only [h0, h17994, h17995, h18976, hlam]
    · linarith only [h0, h17994, h18802, hlam]

set_option maxHeartbeats 13248000 in
set_option maxHeartbeats 13248000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s15_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h17994 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  rcases m.htr 0 2 3 (by decide) (by decide) with h17995 | h17995
  · exact r1l7_11_13_25_L_I_L_I_H_I_s15_x0_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 h17994 h17995
  · exact r1l7_11_13_25_L_I_L_I_H_I_s15_x0_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 h17994 h17995

set_option maxHeartbeats 13248000 in
set_option maxHeartbeats 13248000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s15_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  exact r1l7_11_13_25_L_I_L_I_H_I_s16 m hb1 hb3 hb5 h0 h14799 h16563 h17994

set_option maxHeartbeats 13248000 in
set_option maxHeartbeats 13248000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s15 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  rcases m.htr 0 1 5 (by decide) (by decide) with h17994 | h17994
  · exact r1l7_11_13_25_L_I_L_I_H_I_s15_x0 m hb1 hb3 hb5 hg0 hg14799 hg16563 h17994
  · exact r1l7_11_13_25_L_I_L_I_H_I_s15_x1 m hb1 hb3 hb5 hg0 hg14799 hg16563 h17994

end R2N4
