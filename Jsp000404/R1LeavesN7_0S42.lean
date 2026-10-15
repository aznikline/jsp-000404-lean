import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S40
import Jsp000404.R1LeavesN7_0S41

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x1_x1 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h25260 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 1 4 5 (by decide) (by decide) with h25748 | h25748
  · rcases m.htr 2 3 4 (by decide) (by decide) with h25749 | h25749
    · rcases m.htr 2 3 5 (by decide) (by decide) with h25750 | h25750
      · rcases m.htr 2 4 5 (by decide) (by decide) with h25751 | h25751
        · rcases m.htr 3 4 5 (by decide) (by decide) with h25752 | h25752
          · rcases h1bigk with h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c | h25753c
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              rcases p25753_3 (m.d 0 1) (by simp) with h25755 | h25755
              · rcases p25753_3 (m.d 1 2) (by simp) with h25756 | h25756
                · linarith only [h25756, hlam, p25753_0]
                · rcases p25753_3 (m.d 1 3) (by simp) with h25758 | h25758
                  · linarith only [h1, h25758, hlam]
                  · linarith only [h23340, h25758, hlam]
              · linarith only [h25755, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              rcases p25753_3 (m.d 0 1) (by simp) with h25762 | h25762
              · rcases p25753_3 (m.d 1 2) (by simp) with h25763 | h25763
                · linarith only [h0, h25763, hlam]
                · rcases p25753_3 (m.d 1 3) (by simp) with h25765 | h25765
                  · linarith only [h25765, hlam, p25753_0]
                  · rcases p25753_3 (m.d 1 4) (by simp) with h25767 | h25767
                    · linarith only [h2, h25767, hlam]
                    · linarith only [h23346, h25767, hlam]
              · linarith only [h25762, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              rcases p25753_3 (m.d 0 1) (by simp) with h25771 | h25771
              · rcases p25753_3 (m.d 1 2) (by simp) with h25772 | h25772
                · linarith only [h0, h25772, hlam]
                · rcases p25753_3 (m.d 1 3) (by simp) with h25774 | h25774
                  · linarith only [h1, h25774, hlam]
                  · rcases p25753_3 (m.d 1 4) (by simp) with h25776 | h25776
                    · linarith only [h25776, hlam, p25753_0]
                    · rcases p25753_3 (m.d 1 5) (by simp) with h25778 | h25778
                      · linarith only [h25778, h3, hlam]
                      · rcases h1emax with h25780 | h25780 | h25780 | h25780 | h25780
                        · linarith only [h1, h23337, h25260, h25752, h25780, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases h2bigk with h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c | h25782c
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h22010, h25749, h25751, hc12, hc23, hlam, hphi, p25782_1]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h4, hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h19744, hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h22010, hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h0, hlam, p25782_1]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h23340, hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h23342, hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h23344, hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            rcases p25782_3 (m.d 0 2) (by simp) with h25793 | h25793
                            · linarith only [h25793, hlam, p25782_0]
                            · rcases p25782_3 (m.d 1 2) (by simp) with h25795 | h25795
                              · linarith only [h23340, h25795, hlam]
                              · rcases p25782_3 (m.d 2 3) (by simp) with h25797 | h25797
                                · rcases p25782_3 (m.d 2 4) (by simp) with h25798 | h25798
                                  · linarith only [h25749, h25798, hlam]
                                  · linarith only [h19744, h25798, hlam]
                                · linarith only [h25797, hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            rcases p25782_3 (m.d 0 2) (by simp) with h25802 | h25802
                            · linarith only [h25802, h4, hlam]
                            · linarith only [h0, h25802, hlam]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p25782_1]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p25782_1]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            rcases p25782_3 (m.d 0 2) (by simp) with h25808 | h25808
                            · linarith only [h25808, hlam, p25782_0]
                            · rcases p25782_3 (m.d 1 2) (by simp) with h25810 | h25810
                              · linarith only [h23342, h25810, hlam]
                              · rcases p25782_3 (m.d 2 3) (by simp) with h25812 | h25812
                                · rcases p25782_3 (m.d 2 4) (by simp) with h25813 | h25813
                                  · rcases p25782_3 (m.d 2 5) (by simp) with h25814 | h25814
                                    · linarith only [h25751, h25814, hlam]
                                    · linarith only [h22010, h25814, hlam]
                                  · linarith only [h25813, hlam, p25782_0]
                                · linarith only [h25812, h4, hlam]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            rcases p25782_3 (m.d 0 2) (by simp) with h25819 | h25819
                            · linarith only [h19744, h25819, hlam]
                            · linarith only [h0, h25819, hlam]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h25749, hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h22010, h23338, h23340, h25260, hc12, hc24, hlam, hphi, p25782_1]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            rcases p25782_3 (m.d 0 2) (by simp) with h25825 | h25825
                            · linarith only [h25825, hlam, p25782_0]
                            · rcases p25782_3 (m.d 1 2) (by simp) with h25827 | h25827
                              · linarith only [h23344, h25827, hlam]
                              · rcases p25782_3 (m.d 2 3) (by simp) with h25829 | h25829
                                · rcases p25782_3 (m.d 2 4) (by simp) with h25830 | h25830
                                  · rcases p25782_3 (m.d 2 5) (by simp) with h25831 | h25831
                                    · rcases h4bigk with h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c | h25832c
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        rcases p25832_3 (m.d 0 4) (by simp) with h25834 | h25834
                                        · rcases p25832_3 (m.d 1 4) (by simp) with h25835 | h25835
                                          · linarith only [h2, h25835, hlam]
                                          · rcases p25832_3 (m.d 2 4) (by simp) with h25837 | h25837
                                            · rcases p25832_3 (m.d 3 4) (by simp) with h25838 | h25838
                                              · linarith only [h23337, h25838, hlam]
                                              · linarith only [h23346, h25838, hlam]
                                            · linarith only [h23342, h25837, hlam]
                                        · linarith only [h2, h25834, hlam]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h19744, hlam, p25832_1]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h23337, h23340, h25260, h25752, h4, hc12, hc23, hlam, hphi, p25832_1]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        rcases p25832_3 (m.d 0 4) (by simp) with h25845 | h25845
                                        · rcases p25832_3 (m.d 1 4) (by simp) with h25846 | h25846
                                          · linarith only [h2, h25846, hlam]
                                          · linarith only [h25748, h25846, hlam]
                                        · linarith only [h25845, hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h2, hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h23342, hlam, p25832_1]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h23346, hlam, p25832_1]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p25753_1, p25832_1]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h23337, h23340, h25260, h25749, h25752, hc12, hc23, hlam, hphi, p25832_1]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        rcases p25832_3 (m.d 0 4) (by simp) with h25856 | h25856
                                        · linarith only [h19744, h25856, hlam]
                                        · linarith only [h2, h25856, hlam]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h23340, h25260, h25749, h25752, hc12, hc23, hlam, hphi, p25832_1]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        rcases p25832_3 (m.d 0 4) (by simp) with h25861 | h25861
                                        · linarith only [h19744, h25861, hlam]
                                        · linarith only [h23339, h25861, hlam]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h23337, hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h23337, h25748, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25832_1]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h25749, hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        rcases p25832_3 (m.d 0 4) (by simp) with h25868 | h25868
                                        · rcases p25832_3 (m.d 1 4) (by simp) with h25869 | h25869
                                          · linarith only [h23346, h25869, hlam]
                                          · linarith only [h25748, h25869, hlam]
                                        · linarith only [h23339, h25868, hlam]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h23339, hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h25748, hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h25751, hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [h25752, hlam, p25832_0]
                                      · have p25832_0 := h25832c.1
                                        have p25832_1 := h25832c.2.1
                                        have p25832_2 := h25832c.2.2.1
                                        have p25832_3 := h25832c.2.2.2
                                        linarith only [hlam, p25832_0]
                                    · linarith only [h25831, hlam, p25782_0]
                                  · linarith only [h19744, h25830, hlam]
                                · linarith only [h25829, h4, hlam]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            rcases p25782_3 (m.d 0 2) (by simp) with h25881 | h25881
                            · linarith only [h22010, h25881, hlam]
                            · linarith only [h0, h25881, hlam]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h25750, hlam, p25782_0]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [h25751, hlam, p25782_1]
                          · have p25782_0 := h25782c.1
                            have p25782_1 := h25782c.2.1
                            have p25782_2 := h25782c.2.2.1
                            have p25782_3 := h25782c.2.2.2
                            linarith only [hlam, p25782_0]
                        · rcases h2bigk with h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c | h25887c
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p25887_1]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h4, hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h19744, hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h22010, hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h0, hlam, p25887_1]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h23340, hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h23342, hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h23344, hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            rcases p25887_3 (m.d 0 2) (by simp) with h25898 | h25898
                            · linarith only [h25898, hlam, p25887_0]
                            · rcases p25887_3 (m.d 1 2) (by simp) with h25900 | h25900
                              · linarith only [h23340, h25900, hlam]
                              · rcases p25887_3 (m.d 2 3) (by simp) with h25902 | h25902
                                · rcases p25887_3 (m.d 2 4) (by simp) with h25903 | h25903
                                  · linarith only [h25749, h25903, hlam]
                                  · linarith only [h19744, h25903, hlam]
                                · linarith only [h25902, hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            rcases p25887_3 (m.d 0 2) (by simp) with h25907 | h25907
                            · linarith only [h25907, h4, hlam]
                            · linarith only [h0, h25907, hlam]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p25887_1]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h22010, h23338, h23340, h25260, hc12, hc23, hlam, hphi, p25887_1]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            rcases p25887_3 (m.d 0 2) (by simp) with h25913 | h25913
                            · linarith only [h25913, hlam, p25887_0]
                            · rcases p25887_3 (m.d 1 2) (by simp) with h25915 | h25915
                              · linarith only [h23342, h25915, hlam]
                              · rcases p25887_3 (m.d 2 3) (by simp) with h25917 | h25917
                                · rcases p25887_3 (m.d 2 4) (by simp) with h25918 | h25918
                                  · rcases p25887_3 (m.d 2 5) (by simp) with h25919 | h25919
                                    · linarith only [h25751, h25919, hlam]
                                    · linarith only [h22010, h25919, hlam]
                                  · linarith only [h25918, hlam, p25887_0]
                                · linarith only [h25917, h4, hlam]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            rcases p25887_3 (m.d 0 2) (by simp) with h25924 | h25924
                            · linarith only [h19744, h25924, hlam]
                            · linarith only [h0, h25924, hlam]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h25749, hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h22010, h23338, h23340, h25260, hc12, hc24, hlam, hphi, p25887_1]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            rcases p25887_3 (m.d 0 2) (by simp) with h25930 | h25930
                            · linarith only [h25930, hlam, p25887_0]
                            · rcases p25887_3 (m.d 1 2) (by simp) with h25932 | h25932
                              · linarith only [h23344, h25932, hlam]
                              · rcases p25887_3 (m.d 2 3) (by simp) with h25934 | h25934
                                · rcases p25887_3 (m.d 2 4) (by simp) with h25935 | h25935
                                  · rcases p25887_3 (m.d 2 5) (by simp) with h25936 | h25936
                                    · rcases h4bigk with h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c | h25937c
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        rcases p25937_3 (m.d 0 4) (by simp) with h25939 | h25939
                                        · rcases p25937_3 (m.d 1 4) (by simp) with h25940 | h25940
                                          · linarith only [h2, h25940, hlam]
                                          · rcases p25937_3 (m.d 2 4) (by simp) with h25942 | h25942
                                            · rcases p25937_3 (m.d 3 4) (by simp) with h25943 | h25943
                                              · linarith only [h23337, h25943, hlam]
                                              · linarith only [h23346, h25943, hlam]
                                            · linarith only [h23342, h25942, hlam]
                                        · linarith only [h2, h25939, hlam]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h19744, hlam, p25937_1]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h23337, h23340, h23346, h4, hc12, hc23, hlam, hphi, p25937_1]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        rcases p25937_3 (m.d 0 4) (by simp) with h25950 | h25950
                                        · rcases p25937_3 (m.d 1 4) (by simp) with h25951 | h25951
                                          · linarith only [h2, h25951, hlam]
                                          · linarith only [h25748, h25951, hlam]
                                        · linarith only [h25950, hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h2, hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h23342, hlam, p25937_1]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h23346, hlam, p25937_1]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p25753_1, p25937_1]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h23337, h23340, h25260, h25749, h25752, hc12, hc23, hlam, hphi, p25937_1]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        rcases p25937_3 (m.d 0 4) (by simp) with h25961 | h25961
                                        · linarith only [h19744, h25961, hlam]
                                        · linarith only [h2, h25961, hlam]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h23340, h25260, h25749, h25752, hc12, hc23, hlam, hphi, p25937_1]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        rcases p25937_3 (m.d 0 4) (by simp) with h25966 | h25966
                                        · linarith only [h19744, h25966, hlam]
                                        · linarith only [h23339, h25966, hlam]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h23337, hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h23337, h25748, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p25937_1]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h25749, hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        rcases p25937_3 (m.d 0 4) (by simp) with h25973 | h25973
                                        · rcases p25937_3 (m.d 1 4) (by simp) with h25974 | h25974
                                          · linarith only [h23346, h25974, hlam]
                                          · linarith only [h25748, h25974, hlam]
                                        · linarith only [h23339, h25973, hlam]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h23339, hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h25748, hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h25751, hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [h25752, hlam, p25937_0]
                                      · have p25937_0 := h25937c.1
                                        have p25937_1 := h25937c.2.1
                                        have p25937_2 := h25937c.2.2.1
                                        have p25937_3 := h25937c.2.2.2
                                        linarith only [hlam, p25937_0]
                                    · linarith only [h25936, hlam, p25887_0]
                                  · linarith only [h19744, h25935, hlam]
                                · linarith only [h25934, h4, hlam]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            rcases p25887_3 (m.d 0 2) (by simp) with h25986 | h25986
                            · linarith only [h22010, h25986, hlam]
                            · linarith only [h0, h25986, hlam]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h25750, hlam, p25887_0]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [h25751, hlam, p25887_1]
                          · have p25887_0 := h25887c.1
                            have p25887_1 := h25887c.2.1
                            have p25887_2 := h25887c.2.2.1
                            have p25887_3 := h25887c.2.2.2
                            linarith only [hlam, p25887_0]
                        · rcases h2bigk with h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c | h25992c
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p25992_1]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h4, hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h19744, hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h22010, hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h0, hlam, p25992_1]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h23340, hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h23342, hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h23344, hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            rcases p25992_3 (m.d 0 2) (by simp) with h26003 | h26003
                            · linarith only [h26003, hlam, p25992_0]
                            · rcases p25992_3 (m.d 1 2) (by simp) with h26005 | h26005
                              · linarith only [h23340, h26005, hlam]
                              · rcases p25992_3 (m.d 2 3) (by simp) with h26007 | h26007
                                · rcases p25992_3 (m.d 2 4) (by simp) with h26008 | h26008
                                  · linarith only [h25749, h26008, hlam]
                                  · linarith only [h19744, h26008, hlam]
                                · linarith only [h26007, hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            rcases p25992_3 (m.d 0 2) (by simp) with h26012 | h26012
                            · linarith only [h26012, h4, hlam]
                            · linarith only [h0, h26012, hlam]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p25992_1]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h0, h22010, hc12, hc23, hlam, hphi, p25992_1]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            rcases p25992_3 (m.d 0 2) (by simp) with h26018 | h26018
                            · linarith only [h26018, hlam, p25992_0]
                            · rcases p25992_3 (m.d 1 2) (by simp) with h26020 | h26020
                              · linarith only [h23342, h26020, hlam]
                              · rcases p25992_3 (m.d 2 3) (by simp) with h26022 | h26022
                                · rcases p25992_3 (m.d 2 4) (by simp) with h26023 | h26023
                                  · rcases p25992_3 (m.d 2 5) (by simp) with h26024 | h26024
                                    · linarith only [h25751, h26024, hlam]
                                    · linarith only [h22010, h26024, hlam]
                                  · linarith only [h26023, hlam, p25992_0]
                                · linarith only [h26022, h4, hlam]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            rcases p25992_3 (m.d 0 2) (by simp) with h26029 | h26029
                            · linarith only [h19744, h26029, hlam]
                            · linarith only [h0, h26029, hlam]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h25749, hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h22010, h23338, h23340, h25260, hc12, hc24, hlam, hphi, p25992_1]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            rcases p25992_3 (m.d 0 2) (by simp) with h26035 | h26035
                            · linarith only [h26035, hlam, p25992_0]
                            · rcases p25992_3 (m.d 1 2) (by simp) with h26037 | h26037
                              · linarith only [h23344, h26037, hlam]
                              · rcases p25992_3 (m.d 2 3) (by simp) with h26039 | h26039
                                · rcases p25992_3 (m.d 2 4) (by simp) with h26040 | h26040
                                  · rcases p25992_3 (m.d 2 5) (by simp) with h26041 | h26041
                                    · rcases h4bigk with h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c | h26042c
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        rcases p26042_3 (m.d 0 4) (by simp) with h26044 | h26044
                                        · rcases p26042_3 (m.d 1 4) (by simp) with h26045 | h26045
                                          · linarith only [h2, h26045, hlam]
                                          · rcases p26042_3 (m.d 2 4) (by simp) with h26047 | h26047
                                            · rcases p26042_3 (m.d 3 4) (by simp) with h26048 | h26048
                                              · linarith only [h23337, h26048, hlam]
                                              · linarith only [h23346, h26048, hlam]
                                            · linarith only [h23342, h26047, hlam]
                                        · linarith only [h2, h26044, hlam]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h19744, hlam, p26042_1]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h19744, h23340, h23346, h25749, hc12, hc23, hlam, hphi, p26042_1]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        rcases p26042_3 (m.d 0 4) (by simp) with h26055 | h26055
                                        · rcases p26042_3 (m.d 1 4) (by simp) with h26056 | h26056
                                          · linarith only [h2, h26056, hlam]
                                          · linarith only [h25748, h26056, hlam]
                                        · linarith only [h26055, hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h2, hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h23342, hlam, p26042_1]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h23346, hlam, p26042_1]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p25753_1, p26042_1]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h23337, h23340, h25260, h25749, h25752, hc12, hc23, hlam, hphi, p26042_1]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        rcases p26042_3 (m.d 0 4) (by simp) with h26066 | h26066
                                        · linarith only [h19744, h26066, hlam]
                                        · linarith only [h2, h26066, hlam]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h23340, h25260, h25749, h25752, hc12, hc23, hlam, hphi, p26042_1]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        rcases p26042_3 (m.d 0 4) (by simp) with h26071 | h26071
                                        · linarith only [h19744, h26071, hlam]
                                        · linarith only [h23339, h26071, hlam]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h23337, hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h23337, h25748, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p26042_1]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h25749, hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        rcases p26042_3 (m.d 0 4) (by simp) with h26078 | h26078
                                        · rcases p26042_3 (m.d 1 4) (by simp) with h26079 | h26079
                                          · linarith only [h23346, h26079, hlam]
                                          · linarith only [h25748, h26079, hlam]
                                        · linarith only [h23339, h26078, hlam]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h23339, hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h25748, hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h25751, hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [h25752, hlam, p26042_0]
                                      · have p26042_0 := h26042c.1
                                        have p26042_1 := h26042c.2.1
                                        have p26042_2 := h26042c.2.2.1
                                        have p26042_3 := h26042c.2.2.2
                                        linarith only [hlam, p26042_0]
                                    · linarith only [h26041, hlam, p25992_0]
                                  · linarith only [h19744, h26040, hlam]
                                · linarith only [h26039, h4, hlam]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            rcases p25992_3 (m.d 0 2) (by simp) with h26091 | h26091
                            · linarith only [h22010, h26091, hlam]
                            · linarith only [h0, h26091, hlam]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h25750, hlam, p25992_0]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [h25751, hlam, p25992_1]
                          · have p25992_0 := h25992c.1
                            have p25992_1 := h25992c.2.1
                            have p25992_2 := h25992c.2.2.1
                            have p25992_3 := h25992c.2.2.2
                            linarith only [hlam, p25992_0]
                        · rcases h2bigk with h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c | h26097c
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h4, hc12, hc23, hlam, hphi, p26097_1]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h4, hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h19744, hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h22010, hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h0, hlam, p26097_1]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h23340, hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h23342, hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h23344, hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            rcases p26097_3 (m.d 0 2) (by simp) with h26108 | h26108
                            · linarith only [h26108, hlam, p26097_0]
                            · rcases p26097_3 (m.d 1 2) (by simp) with h26110 | h26110
                              · linarith only [h23340, h26110, hlam]
                              · rcases p26097_3 (m.d 2 3) (by simp) with h26112 | h26112
                                · rcases p26097_3 (m.d 2 4) (by simp) with h26113 | h26113
                                  · linarith only [h25749, h26113, hlam]
                                  · linarith only [h19744, h26113, hlam]
                                · linarith only [h26112, hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            rcases p26097_3 (m.d 0 2) (by simp) with h26117 | h26117
                            · linarith only [h26117, h4, hlam]
                            · linarith only [h0, h26117, hlam]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h19744, hc02, hc23, hlam, hphi, p26097_1]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h22010, h23338, h23340, h25260, hc12, hc23, hlam, hphi, p26097_1]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            rcases p26097_3 (m.d 0 2) (by simp) with h26123 | h26123
                            · linarith only [h26123, hlam, p26097_0]
                            · rcases p26097_3 (m.d 1 2) (by simp) with h26125 | h26125
                              · linarith only [h23342, h26125, hlam]
                              · rcases p26097_3 (m.d 2 3) (by simp) with h26127 | h26127
                                · rcases p26097_3 (m.d 2 4) (by simp) with h26128 | h26128
                                  · rcases p26097_3 (m.d 2 5) (by simp) with h26129 | h26129
                                    · linarith only [h25751, h26129, hlam]
                                    · linarith only [h22010, h26129, hlam]
                                  · linarith only [h26128, hlam, p26097_0]
                                · linarith only [h26127, h4, hlam]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            rcases p26097_3 (m.d 0 2) (by simp) with h26134 | h26134
                            · linarith only [h19744, h26134, hlam]
                            · linarith only [h0, h26134, hlam]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h25749, hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h22010, h23338, h23340, h25260, hc12, hc24, hlam, hphi, p26097_1]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            rcases p26097_3 (m.d 0 2) (by simp) with h26140 | h26140
                            · linarith only [h26140, hlam, p26097_0]
                            · rcases p26097_3 (m.d 1 2) (by simp) with h26142 | h26142
                              · linarith only [h23344, h26142, hlam]
                              · rcases p26097_3 (m.d 2 3) (by simp) with h26144 | h26144
                                · rcases p26097_3 (m.d 2 4) (by simp) with h26145 | h26145
                                  · rcases p26097_3 (m.d 2 5) (by simp) with h26146 | h26146
                                    · rcases h4bigk with h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c | h26147c
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        rcases p26147_3 (m.d 0 4) (by simp) with h26149 | h26149
                                        · rcases p26147_3 (m.d 1 4) (by simp) with h26150 | h26150
                                          · linarith only [h2, h26150, hlam]
                                          · rcases p26147_3 (m.d 2 4) (by simp) with h26152 | h26152
                                            · rcases p26147_3 (m.d 3 4) (by simp) with h26153 | h26153
                                              · linarith only [h23337, h26153, hlam]
                                              · linarith only [h23346, h26153, hlam]
                                            · linarith only [h23342, h26152, hlam]
                                        · linarith only [h2, h26149, hlam]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h19744, hlam, p26147_1]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h23337, h23340, h23346, h4, hc12, hc23, hlam, hphi, p26147_1]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        rcases p26147_3 (m.d 0 4) (by simp) with h26160 | h26160
                                        · rcases p26147_3 (m.d 1 4) (by simp) with h26161 | h26161
                                          · linarith only [h2, h26161, hlam]
                                          · linarith only [h25748, h26161, hlam]
                                        · linarith only [h26160, hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h2, hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h23342, hlam, p26147_1]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h23346, hlam, p26147_1]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p25753_1, p26147_1]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h23337, h23340, h25260, h25749, h25752, hc12, hc23, hlam, hphi, p26147_1]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        rcases p26147_3 (m.d 0 4) (by simp) with h26171 | h26171
                                        · linarith only [h19744, h26171, hlam]
                                        · linarith only [h2, h26171, hlam]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h23340, h25260, h25749, h25752, hc12, hc23, hlam, hphi, p26147_1]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        rcases p26147_3 (m.d 0 4) (by simp) with h26176 | h26176
                                        · linarith only [h19744, h26176, hlam]
                                        · linarith only [h23339, h26176, hlam]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h23337, hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h23337, h25748, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p26147_1]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h25749, hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        rcases p26147_3 (m.d 0 4) (by simp) with h26183 | h26183
                                        · rcases p26147_3 (m.d 1 4) (by simp) with h26184 | h26184
                                          · linarith only [h23346, h26184, hlam]
                                          · linarith only [h25748, h26184, hlam]
                                        · linarith only [h23339, h26183, hlam]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h23339, hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h25748, hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h25751, hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [h25752, hlam, p26147_0]
                                      · have p26147_0 := h26147c.1
                                        have p26147_1 := h26147c.2.1
                                        have p26147_2 := h26147c.2.2.1
                                        have p26147_3 := h26147c.2.2.2
                                        linarith only [hlam, p26147_0]
                                    · linarith only [h26146, hlam, p26097_0]
                                  · linarith only [h19744, h26145, hlam]
                                · linarith only [h26144, h4, hlam]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            rcases p26097_3 (m.d 0 2) (by simp) with h26196 | h26196
                            · linarith only [h22010, h26196, hlam]
                            · linarith only [h0, h26196, hlam]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h25750, hlam, p26097_0]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [h25751, hlam, p26097_1]
                          · have p26097_0 := h26097c.1
                            have p26097_1 := h26097c.2.1
                            have p26097_2 := h26097c.2.2.1
                            have p26097_3 := h26097c.2.2.2
                            linarith only [hlam, p26097_0]
              · linarith only [h25771, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              rcases p25753_3 (m.d 0 1) (by simp) with h26203 | h26203
              · rcases p25753_3 (m.d 1 2) (by simp) with h26204 | h26204
                · linarith only [h0, h26204, hlam]
                · rcases p25753_3 (m.d 1 3) (by simp) with h26206 | h26206
                  · linarith only [h1, h26206, hlam]
                  · rcases p25753_3 (m.d 1 4) (by simp) with h26208 | h26208
                    · linarith only [h2, h26208, hlam]
                    · linarith only [h25748, h26208, hlam]
              · linarith only [h26203, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h0, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h23340, hlam, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h23342, hlam, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h23344, hlam, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h1, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h25260, hc12, hc35, hlam, hphi, ht23, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h23346, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h25260, hlam, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h2, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h23337, h23346, h4, hc12, hc23, hlam, hphi, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h23337, h23340, h23346, h4, hc12, hc23, hlam, hphi, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h23337, h23340, h23346, h25260, h4, hc12, hc23, hlam, hphi, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h3, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h23338, h25260, h4, hc12, hc23, hlam, hphi, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h23338, h23340, h25260, h4, hc12, hc23, hlam, hphi, p25753_1]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [h25748, hlam, p25753_0]
            · have p25753_0 := h25753c.1
              have p25753_1 := h25753c.2.1
              have p25753_2 := h25753c.2.2.1
              have p25753_3 := h25753c.2.2.2
              linarith only [hlam, p25753_0]
          · linarith only [h19744, h23339, h23340, h23346, h25749, h25752, hc12, hc23, hlam, hphi]
        · linarith only [h19744, h2, h25748, h25751, hlam]
      · linarith only [h19744, h23337, h23338, h23339, h23340, h23346, h25750, h4, hc12, hc24, hlam, hphi]
    · linarith only [h23337, h25749, h4, hlam]
  · rcases m.htr 2 3 4 (by decide) (by decide) with h26236 | h26236
    · rcases m.htr 2 3 5 (by decide) (by decide) with h26237 | h26237
      · rcases m.htr 2 4 5 (by decide) (by decide) with h26238 | h26238
        · rcases m.htr 3 4 5 (by decide) (by decide) with h26239 | h26239
          · linarith only [h23337, h23342, h25748, h26239, h4, hc12, hc23, hlam, hphi]
          · linarith only [h23337, h23339, h23340, h23346, h26239, h4, hc12, hc23, hlam, hphi]
        · linarith only [h0, h19744, h23337, h23339, h26238, h4, hc12, hc23, hlam, hphi]
      · linarith only [h23338, h26237, h4, hlam]
    · linarith only [h23337, h26236, h4, hlam]

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x1 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h23346 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 1 3 5 (by decide) (by decide) with h25260 | h25260
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x1_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h25260
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x1_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346 h25260

set_option maxHeartbeats 5798000 in
set_option maxHeartbeats 5798000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (hg23344 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  have h23344 := hg23344
  rcases m.htr 1 3 4 (by decide) (by decide) with h23346 | h23346
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x0 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29_x1 m hb1 hb2 hb4 hb5 hg0 hg1 hg2 hg3 hg4 hg19744 hg22010 hg23337 hg23338 hg23339 hg23340 hg23342 hg23344 h23346

set_option maxHeartbeats 5802000 in
set_option maxHeartbeats 5802000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s28 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (hg23342 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  have h23342 := hg23342
  rcases m.htr 1 2 5 (by decide) (by decide) with h23344 | h23344
  · linarith only [h0, h22010, h23344, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s29 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h19744 h22010 h23337 h23338 h23339 h23340 h23342 h23344

set_option maxHeartbeats 5806000 in
set_option maxHeartbeats 5806000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s27 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (hg23340 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  have h23340 := hg23340
  rcases m.htr 1 2 4 (by decide) (by decide) with h23342 | h23342
  · linarith only [h0, h19744, h23342, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s28 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h19744 h22010 h23337 h23338 h23339 h23340 h23342

set_option maxHeartbeats 5810000 in
set_option maxHeartbeats 5810000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s26 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  have h23339 := hg23339
  rcases m.htr 1 2 3 (by decide) (by decide) with h23340 | h23340
  · linarith only [h0, h23340, h4, hlam]
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s27 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h19744 h22010 h23337 h23338 h23339 h23340

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x0 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s26 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h19744 h22010 h23337 h23338 h23339

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x0 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  linarith only [h0, h26245, h4, hlam]

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x0 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  linarith only [h0, h19744, h26247, hlam]

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x0 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  linarith only [h0, h22010, h26249, hlam]

set_option maxHeartbeats 10410000 in
set_option maxHeartbeats 10410000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s25_x1_x1_x1_x1_x0_x0_x0 (m : N7Model)
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
    (hg22010 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg23337 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg23338 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h23339 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h26245 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h26247 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h26249 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h26251 : (m.d 1 3 + m.lam ≤ m.d 3 4 ∧ m.d 1 3 < m.d 1 4 ∧ m.d 1 4 < m.d 3 4))
    (h26252 : (m.d 1 3 + m.lam ≤ m.d 3 5 ∧ m.d 1 3 < m.d 1 5 ∧ m.d 1 5 < m.d 3 5))
    (h26253 : (m.d 1 4 + m.lam ≤ m.d 4 5 ∧ m.d 1 4 < m.d 1 5 ∧ m.d 1 5 < m.d 4 5))
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
  have h22010 := hg22010
  have h23337 := hg23337
  have h23338 := hg23338
  linarith only [h2, h23339, h26253, hlam]

end R2N4
